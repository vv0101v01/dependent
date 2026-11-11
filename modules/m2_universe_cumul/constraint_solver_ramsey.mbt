///|
/// Module M2 — Algebraic Universe Constraint Graph Solver:
/// 1. Global Axiom (Galois Connection between Constraint Sets Ψ and Valuations N^V)
/// 2. O(1) 64-Variable Bit-Matrix Reachability Accelerator (`reach64`)
/// 3. Tarjan O(V + E) Strongly Connected Components + DAG Longest-Path Minimal Valuation
/// 4. Exact Polynomial Refutation Entailment Checker `Ψ |= ℓ_1 <= ℓ_2` over Full `max`/`+k` Algebra
/// 5. Local Axiom (Fourier-Motzkin Existential Private Universe Variable Elimination)
/// 6. Ramsey-Dilworth Poset Stratification (Maximum Strict Chain & Incomparable Antichain).

///|
#derive(Eq, Debug)
pub(all) struct DiffEdge {
  /// Represents `val(src) + weight <= val(dst)` where vertex 0 is fixed ROOT (`val(0) = 0`)
  /// and universe variable `u >= 0` corresponds to graph vertex `u + 1`.
  src : Int32
  dst : Int32
  weight : Int32
}

///|
pub extend DiffEdge with Eq::{equal, not_equal}

///|
pub extend DiffEdge with @debug.Debug::{to_repr}

///|
pub(all) struct UniverseGraph {
  mut num_vars : Int32
  edges : Array[DiffEdge]
  /// Bit-parallel transitive closure for `val(u) <= val(v)` (weight >= 0) across first 64 vars:
  /// bit `v` in `reach64[u]` is 1 iff `val(u) <= val(v)` is derivable!
  reach64 : FixedArray[UInt64]
}

///|
pub fn UniverseGraph::new(initial_vars : Int32) -> UniverseGraph {
  let n = if initial_vars >= 0 { initial_vars } else { 0 }
  let reach = FixedArray::make(64, 0UL)
  for i = 0; i < 64; i = i + 1 {
    reach[i] = 1UL << i
  }
  let g = { num_vars: 0, edges: [], reach64: reach, }
  for u = 0; u < n; u = u + 1 {
    let _ = g.fresh_var()
  }
  g
}

///|
pub fn UniverseGraph::fresh_var(self : UniverseGraph) -> Int32 {
  let u = self.num_vars
  self.num_vars = u + 1
  // Non-negativity: ROOT (0) + 0 <= (u + 1)
  self.edges.push({ src: 0, dst: u + 1, weight: 0, })
  u
}

///|
fn UniverseGraph::ensure_var(self : UniverseGraph, u : Int32) -> Unit {
  while self.num_vars <= u {
    let _ = self.fresh_var()
  }
}

///|
fn UniverseGraph::record_reach64(
  self : UniverseGraph,
  u : Int32,
  v : Int32,
) -> Unit {
  if u < 0 || u >= 64 || v < 0 || v >= 64 {
    return
  }
  if (self.reach64[u] & (1UL << v)) != 0UL {
    return
  }
  // Incremental O(64) word-parallel transitive closure update:
  // Every ancestor `a` that reaches `u` now reaches everything `v` reaches!
  let v_reach = self.reach64[v]
  for a = 0; a < 64; a = a + 1 {
    if (self.reach64[a] & (1UL << u)) != 0UL {
      self.reach64[a] = self.reach64[a] | v_reach
    }
  }
}

///|
/// O(1) hardware bit-test for `u <= v` among universe variables `0 .. 63`!
pub fn UniverseGraph::fast_le_vars(
  self : UniverseGraph,
  u : Int32,
  v : Int32,
) -> Bool {
  if u == v && u >= 0 {
    return true
  }
  if u >= 0 && u < 64 && v >= 0 && v < 64 {
    (self.reach64[u] & (1UL << v)) != 0UL
  } else {
    false
  }
}

///|
/// Add constraint `u + offset <= v` (e.g. `offset = 0` for `u <= v`, `offset = 1` for `u < v`).
pub fn UniverseGraph::add_var_le(
  self : UniverseGraph,
  u : Int32,
  offset : Int32,
  v : Int32,
) -> Unit raise UniverseError {
  if u < 0 {
    raise UniverseError::InvalidUniverseVar(u)
  }
  if v < 0 {
    raise UniverseError::InvalidUniverseVar(v)
  }
  self.ensure_var(u)
  self.ensure_var(v)
  self.edges.push({ src: u + 1, dst: v + 1, weight: offset, })
  if offset >= 0 {
    self.record_reach64(u, v)
  }
}

///|
/// Add equality constraint `u == v`.
pub fn UniverseGraph::add_var_eq(
  self : UniverseGraph,
  u : Int32,
  v : Int32,
) -> Unit raise UniverseError {
  self.add_var_le(u, 0, v)
  self.add_var_le(v, 0, u)
}

///|
/// Add concrete floor `c <= u`.
pub fn UniverseGraph::add_const_floor(
  self : UniverseGraph,
  c : Int32,
  u : Int32,
) -> Unit raise UniverseError {
  if u < 0 {
    raise UniverseError::InvalidUniverseVar(u)
  }
  self.ensure_var(u)
  if c > 0 {
    self.edges.push({ src: 0, dst: u + 1, weight: c, })
  }
}

///|
/// Add concrete ceiling `u <= c`.
pub fn UniverseGraph::add_const_ceiling(
  self : UniverseGraph,
  u : Int32,
  c : Int32,
) -> Unit raise UniverseError {
  if u < 0 {
    raise UniverseError::InvalidUniverseVar(u)
  }
  if c < 0 {
    raise UniverseError::NegativeConcreteLevel(c)
  }
  self.ensure_var(u)
  self.edges.push({ src: u + 1, dst: 0, weight: -c, })
}

///|
/// Add algebraic constraint `lhs <= u` where `lhs` is any `AlgLevel` and `u` is a universe variable.
pub fn UniverseGraph::add_alg_le_var(
  self : UniverseGraph,
  lhs : AlgLevel,
  rhs_var : Int32,
) -> Unit raise UniverseError {
  self.add_const_floor(lhs.const_floor, rhs_var)
  for item in lhs.var_offsets {
    let (u, off) = item
    self.add_var_le(u, off, rhs_var)
  }
}

///|
/// Tarjan O(V + E) Strongly Connected Components + Longest-Path Solver for pure non-negative
/// difference graphs, seamlessly backed by Bellman-Ford-Moore SPFA when negative ceiling/refutation
/// weights are present. Returns the unique point-wise LEAST natural valuation `v_min[u] >= 0`,
/// or raises `UniverseCycleDetected` if inconsistent!
pub fn UniverseGraph::solve_minimal_valuation(
  self : UniverseGraph,
) -> Array[Int32] raise UniverseError {
  solve_edges_valuation(self.num_vars, self.edges)
}

///|
fn solve_edges_valuation(
  num_vars : Int32,
  edges : Array[DiffEdge],
) -> Array[Int32] raise UniverseError {
  let n_verts = num_vars + 1
  let mut has_neg = false
  for e in edges {
    if e.weight < 0 {
      has_neg = true
      break
    }
  }
  if !has_neg {
    return solve_nonneg_tarjan_dag(num_vars, n_verts, edges)
  }
  solve_general_spfa(num_vars, n_verts, edges)
}

///|
fn solve_nonneg_tarjan_dag(
  num_vars : Int32,
  n_verts : Int32,
  edges : Array[DiffEdge],
) -> Array[Int32] raise UniverseError {
  let adj : Array[Array[(Int32, Int32)]] = []
  for i = 0; i < n_verts; i = i + 1 {
    let _ = i
    adj.push([])
  }
  for e in edges {
    adj[e.src].push((e.dst, e.weight))
  }
  let dfn = Array::make(n_verts, -1)
  let low = Array::make(n_verts, -1)
  let on_stack = Array::make(n_verts, false)
  let scc_id = Array::make(n_verts, -1)
  let stack : Array[Int32] = []
  let sccs : Array[Array[Int32]] = []
  let timer_box = [0]

  fn tarjan(v : Int32) -> Unit {
    let t = timer_box[0]
    timer_box[0] = t + 1
    dfn[v] = t
    low[v] = t
    stack.push(v)
    on_stack[v] = true
    for next in adj[v] {
      let (w, _) = next
      if dfn[w] == -1 {
        tarjan(w)
        if low[w] < low[v] {
          low[v] = low[w]
        }
      } else if on_stack[w] {
        if dfn[w] < low[v] {
          low[v] = dfn[w]
        }
      }
    }
    if low[v] == dfn[v] {
      let comp : Array[Int32] = []
      let cid = sccs.length()
      while !stack.is_empty() {
        let top = stack.pop().unwrap()
        on_stack[top] = false
        scc_id[top] = cid
        comp.push(top)
        if top == v {
          break
        }
      }
      sccs.push(comp)
    }
  }

  for v = 0; v < n_verts; v = v + 1 {
    if dfn[v] == -1 {
      tarjan(v)
    }
  }

  // Theorem 2.1(a): Check no intra-SCC edge has strictly positive weight `w > 0`:
  for e in edges {
    if scc_id[e.src] == scc_id[e.dst] && e.weight > 0 {
      let cyc : Array[Int32] = []
      for v in sccs[scc_id[e.src]] {
        if v > 0 {
          cyc.push(v - 1)
        }
      }
      raise UniverseError::UniverseCycleDetected(cyc)
    }
  }

  // Tarjan emits SCCs in reverse topological order!
  // Iterating `c = sccs.length() - 1` down to `0` visits SCCs in exact topological order!
  let num_sccs = sccs.length()
  let scc_val = Array::make(num_sccs, 0)
  for c = num_sccs - 1; c >= 0; c = c - 1 {
    let cur_val = scc_val[c]
    for v in sccs[c] {
      for next in adj[v] {
        let (w, wt) = next
        let dst_c = scc_id[w]
        if dst_c != c {
          let cand = cur_val + wt
          if cand > scc_val[dst_c] {
            scc_val[dst_c] = cand
          }
        }
      }
    }
  }
  let root_val = scc_val[scc_id[0]]
  let out = Array::make(num_vars, 0)
  for u = 0; u < num_vars; u = u + 1 {
    out[u] = scc_val[scc_id[u + 1]] - root_val
  }
  out
}

///|
fn solve_general_spfa(
  num_vars : Int32,
  n_verts : Int32,
  edges : Array[DiffEdge],
) -> Array[Int32] raise UniverseError {
  let adj : Array[Array[(Int32, Int32)]] = []
  for i = 0; i < n_verts; i = i + 1 {
    let _ = i
    adj.push([])
  }
  for e in edges {
    adj[e.src].push((e.dst, e.weight))
  }
  // Longest-path relaxation from all vertices (initialized to 0; ROOT=0 stays 0 unless positive cycle hits 0)
  let dist = Array::make(n_verts, 0)
  let in_q = Array::make(n_verts, true)
  let relax_cnt = Array::make(n_verts, 0)
  let queue : Array[Int32] = []
  for v = 0; v < n_verts; v = v + 1 {
    queue.push(v)
  }
  let mut head = 0
  while head < queue.length() {
    let v = queue[head]
    head = head + 1
    in_q[v] = false
    for next in adj[v] {
      let (w, wt) = next
      let cand = dist[v] + wt
      if cand > dist[w] {
        dist[w] = cand
        relax_cnt[w] = relax_cnt[w] + 1
        if relax_cnt[w] > n_verts {
          let cyc = if w > 0 { [w - 1] } else { [] }
          raise UniverseError::UniverseCycleDetected(cyc)
        }
        if !in_q[w] {
          in_q[w] = true
          queue.push(w)
        }
      }
    }
  }
  if dist[0] > 0 {
    raise UniverseError::UniverseCycleDetected([])
  }
  let out = Array::make(num_vars, 0)
  for u = 0; u < num_vars; u = u + 1 {
    out[u] = dist[u + 1] - dist[0]
  }
  out
}

///|
/// Check consistency of the current constraint graph in polynomial time.
pub fn UniverseGraph::is_consistent(self : UniverseGraph) -> Bool {
  try {
    let _ = self.solve_minimal_valuation()
    true
  } catch {
    _ => false
  }
}

///|
/// Global Axiom (Galois Refutation Completeness Theorem):
/// Decides exact semantic entailment `Ψ |= lhs <= rhs` for arbitrary `AlgLevel` expressions!
/// Decomposition: `max_p A_p <= max_q B_q  <=>  ∀p, (A_p <= max_q B_q)`
/// And `Ψ |= (A_p <= max_q B_q)` iff `Ψ ∪ { B_q + 1 <= A_p | ∀q }` is unsatisfiable!
/// Includes O(1) syntactic & `reach64` bitmatrix fast-paths before invoking graph refutation.
pub fn UniverseGraph::entails_le(
  self : UniverseGraph,
  lhs : AlgLevel,
  rhs : AlgLevel,
) -> Bool {
  if lhs == rhs {
    return true
  }
  if !self.is_consistent() {
    return true
  }
  // Check constant floor atom `lhs.const_floor <= rhs`:
  if !self.entails_atom_le_rhs(-1, lhs.const_floor, rhs) {
    return false
  }
  // Check each variable offset atom `u + off <= rhs`:
  for item in lhs.var_offsets {
    let (u, off) = item
    if !self.entails_atom_le_rhs(u, off, rhs) {
      return false
    }
  }
  true
}

///|
fn UniverseGraph::entails_atom_le_rhs(
  self : UniverseGraph,
  lhs_var : Int32,
  lhs_off : Int32,
  rhs : AlgLevel,
) -> Bool {
  // Fast O(1) syntactic & bitmatrix checks!
  if lhs_var == -1 {
    // Constant atom `lhs_off <= rhs`:
    if lhs_off <= rhs.const_floor {
      return true
    }
  } else {
    // Variable atom `u + lhs_off <= rhs`:
    for r_item in rhs.var_offsets {
      let (rv, roff) = r_item
      if lhs_off <= roff && self.fast_le_vars(lhs_var, rv) {
        return true
      }
    }
  }
  // Exact Galois Refutation: test whether `Ψ ∪ { ∀ atom B_q in rhs: B_q + 1 <= A_p }` has a positive cycle!
  let mut max_v = self.num_vars
  if lhs_var >= max_v {
    max_v = lhs_var + 1
  }
  for r_item in rhs.var_offsets {
    if r_item.0 >= max_v {
      max_v = r_item.0 + 1
    }
  }
  let aug = self.edges.copy()
  for v = self.num_vars; v < max_v; v = v + 1 {
    aug.push({ src: 0, dst: v + 1, weight: 0, })
  }
  let target_vert = if lhs_var == -1 { 0 } else { lhs_var + 1 }
  // Negating `lhs_var + lhs_off <= rhs.const_floor` gives `ROOT + (rhs.const_floor + 1 - lhs_off) <= target_vert`
  aug.push({ src: 0, dst: target_vert, weight: rhs.const_floor + 1 - lhs_off, })
  // Negating `lhs_var + lhs_off <= rv + roff` gives `(rv + 1) + (roff + 1 - lhs_off) <= target_vert`
  for r_item in rhs.var_offsets {
    let (rv, roff) = r_item
    aug.push({ src: rv + 1, dst: target_vert, weight: roff + 1 - lhs_off, })
  }
  try {
    let _ = solve_edges_valuation(max_v, aug)
    false
  } catch {
    _ => true
  }
}

///|
/// Unified Subtyping / Conversion Check across HierarchyMode (`Cumulative` vs `NonCumulative`)
/// and Parametric Variance (`Irrelevant`, `Covariant`, `Invariant`).
pub fn UniverseGraph::check_level_rel(
  self : UniverseGraph,
  mode : HierarchyMode,
  variance : Variance,
  lhs : AlgLevel,
  rhs : AlgLevel,
) -> Unit raise UniverseError {
  match variance {
    Irrelevant => ()
    Invariant =>
      if !(self.entails_le(lhs, rhs) && self.entails_le(rhs, lhs)) {
        raise UniverseError::NonCumulativeMismatch(lhs, rhs)
      }
    Covariant =>
      match mode {
        NonCumulative =>
          if !(self.entails_le(lhs, rhs) && self.entails_le(rhs, lhs)) {
            raise UniverseError::NonCumulativeMismatch(lhs, rhs)
          }
        Cumulative =>
          if !self.entails_le(lhs, rhs) {
            raise UniverseError::CumulativeEntailmentFailed(lhs, rhs)
          }
      }
  }
}

///|
/// Local Axiom (Fourier-Motzkin / Transitive Bridge Elimination of Private Universe Variables):
/// Eliminates all private existential universe variables NOT in `public_mask`, projecting
/// the constraint system onto public variables while preserving exact satisfiability & public entailments!
pub fn UniverseGraph::eliminate_private_vars(
  self : UniverseGraph,
  is_public : Array[Bool],
) -> UniverseGraph raise UniverseError {
  // First verify consistency so inconsistent systems aren't silently erased:
  let _ = self.solve_minimal_valuation()
  let mut cur_edges = self.edges.copy()
  for u = 0; u < self.num_vars; u = u + 1 {
    let keep = if u < is_public.length() { is_public[u] } else { false }
    if !keep {
      let elim_vert = u + 1
      let incoming : Array[DiffEdge] = []
      let outgoing : Array[DiffEdge] = []
      let remaining : Array[DiffEdge] = []
      for e in cur_edges {
        if e.src == elim_vert && e.dst == elim_vert {
          if e.weight > 0 {
            raise UniverseError::UniverseCycleDetected([u])
          }
        } else if e.dst == elim_vert {
          incoming.push(e)
        } else if e.src == elim_vert {
          outgoing.push(e)
        } else {
          remaining.push(e)
        }
      }
      // Deduplicate `(src, dst) -> max(weight)` after Fourier-Motzkin bridge `in.src + (in.w + out.w) <= out.dst`
      let best_map : Map[Int64, Int32] = Map([])
      for r in remaining {
        let key = (r.src.to_int64() << 32) | (r.dst.to_int64() & 0xFFFFFFFFL)
        match best_map.get(key) {
          Some(prev) => if r.weight > prev { best_map[key] = r.weight }
          None => best_map[key] = r.weight
        }
      }
      for inc in incoming {
        for out in outgoing {
          let w_sum = inc.weight + out.weight
          if inc.src == out.dst {
            if w_sum > 0 {
              raise UniverseError::UniverseCycleDetected([u])
            }
          } else {
            let key = (inc.src.to_int64() << 32) |
              (out.dst.to_int64() & 0xFFFFFFFFL)
            match best_map.get(key) {
              Some(prev) => if w_sum > prev { best_map[key] = w_sum }
              None => best_map[key] = w_sum
            }
          }
        }
      }
      let next_edges : Array[DiffEdge] = []
      for k, wt in best_map {
        let s = (k >> 32).to_int()
        let d = (k & 0xFFFFFFFFL).to_int()
        next_edges.push({ src: s, dst: d, weight: wt, })
      }
      cur_edges = next_edges
    }
  }
  let out_g = UniverseGraph::new(self.num_vars)
  out_g.edges.clear()
  for e in cur_edges {
    out_g.edges.push(e)
    if e.src > 0 && e.dst > 0 && e.weight >= 0 {
      out_g.record_reach64(e.src - 1, e.dst - 1)
    }
  }
  out_g
}

///|
/// Ramsey-Dilworth Universe Poset Stratification Result:
/// By Mirsky's Dual Dilworth Theorem & Poset Ramsey Theory, on `N` universe variables:
/// - `max_strict_chain`: longest strictly increasing universe chain `u_{i_1} < u_{i_2} < ... < u_{i_h}`
/// - `antichain_layers`: canonical partition into `h` pairwise-incomparable universe antichains
/// - `ramsey_guarantee_holds`: verifies `max_strict_chain.length() * max_antichain_width >= num_vars`
///   (Erdős-Szekeres / Ramsey comparable-vs-incomparable bound!).
#derive(Eq, Debug)
pub(all) struct PosetStratification {
  max_strict_chain : Array[Int32]
  antichain_layers : Array[Array[Int32]]
  max_antichain_width : Int32
  ramsey_bound_holds : Bool
}

///|
pub extend PosetStratification with Eq::{equal, not_equal}

///|
pub extend PosetStratification with @debug.Debug::{to_repr}

///|
/// Compute exact strict-order stratification `u < v <=> Ψ |= u + 1 <= v` on `0 .. num_vars - 1`,
/// extracting maximum strict chain, antichain layer decomposition, and verifying the Erdős-Szekeres / Ramsey bound!
pub fn UniverseGraph::stratify_ramsey_dilworth(
  self : UniverseGraph,
) -> PosetStratification raise UniverseError {
  let _ = self.solve_minimal_valuation()
  let n = self.num_vars
  if n == 0 {
    return {
      max_strict_chain: [],
      antichain_layers: [],
      max_antichain_width: 0,
      ramsey_bound_holds: true,
    }
  }
  // Build strict partial order `strict_lt[u][v] <=> Ψ |= u + 1 <= v`
  let strict_lt : Array[Array[Bool]] = []
  for u = 0; u < n; u = u + 1 {
    let row = Array::make(n, false)
    for v = 0; v < n; v = v + 1 {
      if u != v {
        let lhs = AlgLevel::var_offset(u, 1)
        let rhs = AlgLevel::var_offset(v, 0)
        row[v] = self.entails_le(lhs, rhs)
      }
    }
    strict_lt.push(row)
  }
  // Longest chain DP on the strict DAG (`strict_lt` is irreflexive & transitive, hence a strict DAG!)
  let memo_len = Array::make(n, 0)
  let next_ptr = Array::make(n, -1)

  fn dfs_rank(u : Int32) -> Int32 {
    if memo_len[u] > 0 {
      return memo_len[u]
    }
    let mut best = 1
    let mut best_next = -1
    for v = 0; v < n; v = v + 1 {
      if strict_lt[u][v] {
        let sub = 1 + dfs_rank(v)
        if sub > best {
          best = sub
          best_next = v
        }
      }
    }
    memo_len[u] = best
    next_ptr[u] = best_next
    best
  }

  let mut max_h = 0
  let mut best_start = 0
  for u = 0; u < n; u = u + 1 {
    let r = dfs_rank(u)
    if r > max_h {
      max_h = r
      best_start = u
    }
  }
  let chain : Array[Int32] = []
  let mut cur = best_start
  while cur != -1 {
    chain.push(cur)
    cur = next_ptr[cur]
  }
  // Mirsky's Dual Dilworth Theorem: partitioning elements by `memo_len[u]` yields `max_h` genuine antichains!
  let layers : Array[Array[Int32]] = []
  for l = 0; l < max_h; l = l + 1 {
    let _ = l
    layers.push([])
  }
  for u = 0; u < n; u = u + 1 {
    let layer_idx = max_h - memo_len[u]
    layers[layer_idx].push(u)
  }
  let mut max_w = 0
  for layer in layers {
    if layer.length() > max_w {
      max_w = layer.length()
    }
  }
  let ramsey_ok = chain.length() * max_w >= n
  {
    max_strict_chain: chain,
    antichain_layers: layers,
    max_antichain_width: max_w,
    ramsey_bound_holds: ramsey_ok,
  }
}
