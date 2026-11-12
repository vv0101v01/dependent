///|
/// Module M9 (Part 2):
/// 1. Deep Copattern Observation Tree Coverage & Non-Redundancy Checker (Abel-Pientka-Thibodeau)
/// 2. Sized / Clocked Guarded Later (`▷`) Productivity Checker (Birkedal-Møgelberg `gDTT`)
/// 3. Hopcroft-Karp Union-Find Exact Infinite-Horizon Bisimulation Solver in `O(N α(N))`!

///|
#derive(Eq, Hash, Compare, Debug)
pub(all) enum CopatObs {
  ObsHead
  ObsTail
}

///|
pub extend CopatObs with Eq::{equal, not_equal}

///|
pub extend CopatObs with Hash::{hash_combine, hash}

///|
pub extend CopatObs with Compare::{compare, op_lt, op_le, op_ge, op_gt}

///|
pub extend CopatObs with @debug.Debug::{to_repr}

///|
#derive(Eq, Debug)
pub enum CopatTrie {
  TrieEmpty
  TrieLeaf(Int32)
  TrieSplit(CopatTrie, CopatTrie)
}

///|
pub extend CopatTrie with Eq::{equal, not_equal}

///|
pub extend CopatTrie with @debug.Debug::{to_repr}

///|
fn insert_copat_clause(
  node : CopatTrie,
  path : Array[CopatObs],
  depth : Int32,
  clause_id : Int32,
) -> CopatTrie raise CoalgebraError {
  if depth == path.length() {
    match node {
      TrieEmpty => TrieLeaf(clause_id)
      _ => raise CoalgebraError::RedundantCopatternClause(clause_id)
    }
  } else {
    match node {
      TrieLeaf(_) => raise CoalgebraError::RedundantCopatternClause(clause_id)
      TrieEmpty =>
        match path[depth] {
          ObsHead =>
            TrieSplit(
              insert_copat_clause(TrieEmpty, path, depth + 1, clause_id),
              TrieEmpty,
            )
          ObsTail =>
            TrieSplit(
              TrieEmpty,
              insert_copat_clause(TrieEmpty, path, depth + 1, clause_id),
            )
        }
      TrieSplit(on_hd, on_tl) =>
        match path[depth] {
          ObsHead =>
            TrieSplit(
              insert_copat_clause(on_hd, path, depth + 1, clause_id),
              on_tl,
            )
          ObsTail =>
            TrieSplit(
              on_hd,
              insert_copat_clause(on_tl, path, depth + 1, clause_id),
            )
        }
    }
  }
}

///|
fn verify_trie_exhaustive(
  node : CopatTrie,
  trace : String,
) -> Unit raise CoalgebraError {
  match node {
    TrieEmpty => raise CoalgebraError::UncoveredCopatternPath(trace)
    TrieLeaf(_) => ()
    TrieSplit(on_hd, on_tl) => {
      // Note: `hd` projects out an element of `A` (no further stream observations unless nested stream,
      // here for `Stream A` `hd` must be `TrieLeaf`, while `tl` can either be `TrieLeaf` OR split further!)
      verify_trie_exhaustive(on_hd, trace + ".hd")
      verify_trie_exhaustive(on_tl, trace + ".tl")
    }
  }
}

///|
/// Theorem 9.2 (Deep Copattern Partition Theorem):
/// Verifies that `clauses` forms an exact partition of the stream observation space
/// (every observation chain hits a unique leaf with zero missing projections and zero overlap)!
pub fn check_copattern_coverage(
  clauses : Array[Array[CopatObs]],
) -> CopatTrie raise CoalgebraError {
  let mut trie = TrieEmpty
  for i = 0; i < clauses.length(); i = i + 1 {
    trie = insert_copat_clause(trie, clauses[i], 0, i)
  }
  verify_trie_exhaustive(trie, "root")
  trie
}

///|
/// ============================================================================
/// 2. Sized / Clocked Guarded Later (`▷`) Corecursive Productivity Checker
/// ============================================================================
#derive(Eq, Debug)
pub(all) enum CorecStreamExpr {
  CSConst(Int32)
  CSExtStream(String)
  CSCons(Int32, CorecStreamExpr)
  CSTail(CorecStreamExpr)
  CSMapSucc(CorecStreamExpr)
  CSZipAdd(CorecStreamExpr, CorecStreamExpr)
  CSSelfRef
}

///|
pub extend CorecStreamExpr with Eq::{equal, not_equal}

///|
pub extend CorecStreamExpr with @debug.Debug::{to_repr}

///|
/// Theorem 9.3 (Clocked Guard Credit Productivity Criterion):
/// Computes minimum net constructor guard depth at every `CSSelfRef` occurrence:
/// - `CSCons(_, tail_e)` grants `+1` Later (`▷`) credit (`guard + 1`)
/// - `CSTail(e)` consumes `-1` Later (`▷`) credit (`guard - 1`)
/// - `CSMapSucc` / `CSZipAdd` are size-preserving (`guard + 0`)
/// - `CSSelfRef` requires `guard >= 1`; otherwise raises `UnguardedCorecursiveCall(guard)`!
/// Returns the minimum slack `min_{self} guard >= 1` (or `999999` if non-recursive).
pub fn verify_guarded_productivity(
  expr : CorecStreamExpr,
) -> Int32 raise CoalgebraError {
  fn check_at(
    e : CorecStreamExpr,
    credit : Int32,
  ) -> Int32 raise CoalgebraError {
    match e {
      CSConst(_) | CSExtStream(_) => 999999
      CSSelfRef => {
        if credit < 1 {
          raise CoalgebraError::UnguardedCorecursiveCall(credit)
        }
        credit
      }
      CSCons(_, rest) => check_at(rest, credit + 1)
      CSTail(sub) => check_at(sub, credit - 1)
      CSMapSucc(sub) => check_at(sub, credit)
      CSZipAdd(a, b) => {
        let ga = check_at(a, credit)
        let gb = check_at(b, credit)
        if ga <= gb {
          ga
        } else {
          gb
        }
      }
    }
  }

  check_at(expr, 0)
}

///|
/// ============================================================================
/// 3. Hopcroft-Karp Disjoint-Set Union-Find Exact Coalgebraic Bisimulation Solver
/// ============================================================================
/// Finite-state deterministic stream automaton `M = (num_states, init_state, head_out, tail_next)`.
#derive(Eq, Debug)
pub(all) struct FiniteStreamAutomaton {
  num_states : Int32
  init_state : Int32
  head_out : Array[Int32]
  tail_next : Array[Int32]
}

///|
pub extend FiniteStreamAutomaton with Eq::{equal, not_equal}

///|
pub extend FiniteStreamAutomaton with @debug.Debug::{to_repr}

///|
/// Turn a `FiniteStreamAutomaton` into an infinite `InfStream[Int32]` via `ana_stream`.
pub fn automaton_to_stream(a : FiniteStreamAutomaton) -> InfStream[Int32] {
  ana_stream({
    seed: a.init_state,
    step: fn(s) { (a.head_out[s], a.tail_next[s]) },
  })
}

///|
/// Theorem 9.4 (Hopcroft-Karp Coinductive Bisimulation Up-To Equivalence):
/// Decides EXACT infinite-horizon stream equality `automaton_to_stream(m1) ≈ automaton_to_stream(m2)`
/// in `O((N_1 + N_2) α(N_1 + N_2))` time by maintaining a Union-Find Bisimulation Up-To Equivalence
/// over the disjoint union state space `{0 .. N_1 - 1} ⊔ {N_1 .. N_1 + N_2 - 1}`!
pub fn are_automata_bisimilar(
  m1 : FiniteStreamAutomaton,
  m2 : FiniteStreamAutomaton,
) -> Bool raise CoalgebraError {
  let n1 = m1.num_states
  let n2 = m2.num_states
  if m1.init_state < 0 ||
    m1.init_state >= n1 ||
    m1.head_out.length() != n1 ||
    m1.tail_next.length() != n1 {
    raise CoalgebraError::InvalidAutomatonState(m1.init_state)
  }
  if m2.init_state < 0 ||
    m2.init_state >= n2 ||
    m2.head_out.length() != n2 ||
    m2.tail_next.length() != n2 {
    raise CoalgebraError::InvalidAutomatonState(m2.init_state)
  }
  // Transition totality: every `tail_next` must stay inside the state space,
  // otherwise the union-find exploration would index out of bounds.
  for i = 0; i < n1; i = i + 1 {
    if m1.tail_next[i] < 0 || m1.tail_next[i] >= n1 {
      raise CoalgebraError::InvalidAutomatonState(i)
    }
  }
  for j = 0; j < n2; j = j + 1 {
    if m2.tail_next[j] < 0 || m2.tail_next[j] >= n2 {
      raise CoalgebraError::InvalidAutomatonState(j)
    }
  }

  let total = n1 + n2
  let parent : Array[Int32] = []
  let rank : Array[Int32] = Array::make(total, 0)
  let out_lbl : Array[Int32] = []
  let next_st : Array[Int32] = []
  for i = 0; i < n1; i = i + 1 {
    parent.push(i)
    out_lbl.push(m1.head_out[i])
    next_st.push(m1.tail_next[i])
  }
  for j = 0; j < n2; j = j + 1 {
    parent.push(n1 + j)
    out_lbl.push(m2.head_out[j])
    next_st.push(n1 + m2.tail_next[j])
  }

  fn uf_find(x0 : Int32) -> Int32 {
    let mut r = x0
    while parent[r] != r {
      r = parent[r]
    }
    let mut c = x0
    while parent[c] != r {
      let nxt = parent[c]
      parent[c] = r
      c = nxt
    }
    r
  }

  fn uf_union(a : Int32, b : Int32) -> Unit {
    let ra = uf_find(a)
    let rb = uf_find(b)
    if ra == rb {
      return
    }
    if rank[ra] < rank[rb] {
      parent[ra] = rb
    } else if rank[ra] > rank[rb] {
      parent[rb] = ra
    } else {
      parent[rb] = ra
      rank[ra] = rank[ra] + 1
    }
  }

  let queue : Array[(Int32, Int32)] = [(m1.init_state, n1 + m2.init_state)]
  let mut q_head = 0
  while q_head < queue.length() {
    let (u, v) = queue[q_head]
    q_head = q_head + 1
    let ru = uf_find(u)
    let rv = uf_find(v)
    if ru != rv {
      if out_lbl[u] != out_lbl[v] {
        return false
      }
      uf_union(ru, rv)
      queue.push((next_st[u], next_st[v]))
    }
  }
  true
}
