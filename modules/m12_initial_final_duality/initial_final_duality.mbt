///|
/// Module M12 — Categorical Fusion of M8 (Initial Algebras: SP/IR/II/W) & M9 (Terminal Coalgebras: Streams/Bisim)
/// with M1 (Hash-Consed Arena), M3 (NbE Kernel), and M6 (64-Bit Chu-Galois Duality):
/// 1. Algebra–Coalgebra 64-Bit Chu Space Pairing & Galois Involution
/// 2. Hylomorphism Deforestation (`hylo = cata ∘ ana` without intermediate `WTree` allocation)
/// 3. Localization `Coalg[Bisim^-1]` via Canonical Quotient Minimization + O(1) M1 Arena Interning
/// 4. Functorial Reflection of M8 Inductive-Inductive `(IICtx, IITy)` into M3 NbE Kernel!

///|
pub(all) suberror DualityError {
  UnfoldDepthExceeded(Int32)
  ChuSizeExceeded(Int32)
  HyloFusionDisagreement
}

///|
/// 1. Evaluate a Finite Inductive Observation Tree `WTree[(Int32, Int32)]` (`(step_offset, threshold)`)
/// against an Infinite Coalgebraic Stream `InfStream[Int32]`, building a 64-Bit M6 `ChuTypingSpace`!
/// Here `w = WSup((idx, bound), sub_obs)` holds on stream `s` iff `s[idx] >= bound` AND all `sub_obs` hold on `tl(s)`!
pub fn eval_w_pattern_on_stream(
  pat : @m8.WTree[(Int32, Int32)],
  s : @m9.InfStream[Int32],
) -> Bool raise Error {
  match pat {
    WSup((idx, min_val), kids) => {
      let v = @m9.stream_nth(idx, s)
      if v < min_val {
        return false
      }
      let next_s = @m9.stream_tl(s)
      for k in kids {
        if !eval_w_pattern_on_stream(k, next_s) {
          return false
        }
      }
      true
    }
  }
}

///|
pub fn build_algebra_coalgebra_chu(
  w_patterns : Array[@m8.WTree[(Int32, Int32)]],
  streams : Array[@m9.InfStream[Int32]],
) -> @m6.ChuTypingSpace raise Error {
  let m = w_patterns.length()
  let n = streams.length()
  if m > 64 {
    raise DualityError::ChuSizeExceeded(m)
  }
  if n > 64 {
    raise DualityError::ChuSizeExceeded(n)
  }
  let rows : Array[UInt64] = Array::make(m, 0UL)
  let cols : Array[UInt64] = Array::make(n, 0UL)
  for a = 0; a < m; a = a + 1 {
    for x = 0; x < n; x = x + 1 {
      if eval_w_pattern_on_stream(w_patterns[a], streams[x]) {
        rows[a] = rows[a] | (1UL << x)
        cols[x] = cols[x] | (1UL << a)
      }
    }
  }
  { num_terms: m, num_types: n, rows, cols, }
}

///|
/// 2. Bounded Anamorphism into `WTree[S]` (`ana_w`) & Deforested Hylomorphism (`hylo_deforest`):
/// Theorem 12.2 (Meijer-Fokkinga-Paterson Hylomorphism Fusion):
/// Eliminates all intermediate `WTree[S]` heap nodes (`hylo_deforest == cata_w ∘ ana_w`)!
pub fn[Seed, S] ana_w(
  coalg : (Seed) -> (S, Array[Seed]),
  seed : Seed,
  fuel : Int32,
) -> @m8.WTree[S] raise DualityError {
  if fuel <= 0 {
    raise DualityError::UnfoldDepthExceeded(fuel)
  }
  let (shape, next_seeds) = coalg(seed)
  let kids : Array[@m8.WTree[S]] = []
  for ns in next_seeds {
    kids.push(ana_w(coalg, ns, fuel - 1))
  }
  WSup(shape, kids)
}

///|
pub fn[Seed, S, R] hylo_deforest(
  coalg : (Seed) -> (S, Array[Seed]),
  alg : (S, Array[R]) -> R,
  seed : Seed,
  fuel : Int32,
) -> R raise DualityError {
  if fuel <= 0 {
    raise DualityError::UnfoldDepthExceeded(fuel)
  }
  let (shape, next_seeds) = coalg(seed)
  let mapped : Array[R] = []
  for ns in next_seeds {
    mapped.push(hylo_deforest(coalg, alg, ns, fuel - 1))
  }
  alg(shape, mapped)
}

///|
/// 3. Localization of Finite-State Stream Coalgebras `Coalg[Bisim^-1]` (`組合範例.md` #12):
/// Minimizes any reachable `FiniteStreamAutomaton` modulo exact bisimulation (via Hopcroft-Karp `are_automata_bisimilar`
/// + BFS canonical state relabeling `0, 1, ..., k-1` from `init_state`) and interns the resulting canonical
/// normal-form syntax tree into M1's Hash-Consed `SyntaxArena`!
/// Theorem 12.3 (Localization Soundness & Completeness):
/// `are_automata_bisimilar(m1, m2) == true  <==>  localize_automaton_in_arena(arena, m1) == localize_automaton_in_arena(arena, m2)`!
pub fn minimize_stream_coalgebra(
  aut : @m9.FiniteStreamAutomaton,
) -> @m9.FiniteStreamAutomaton raise Error {
  // Step 1: Partition states `0 .. n-1` into exact bisimulation equivalence classes using M9's `are_automata_bisimilar`!
  let n = aut.num_states
  let rep_of : Array[Int32] = Array::make(n, -1)
  let reps : Array[Int32] = []
  for s = 0; s < n; s = s + 1 {
    let as_s : @m9.FiniteStreamAutomaton = {
      num_states: n,
      init_state: s,
      head_out: aut.head_out,
      tail_next: aut.tail_next,
    }
    let mut matched_rep = -1
    for r in reps {
      let as_r : @m9.FiniteStreamAutomaton = {
        num_states: n,
        init_state: r,
        head_out: aut.head_out,
        tail_next: aut.tail_next,
      }
      if @m9.are_automata_bisimilar(as_s, as_r) {
        matched_rep = r
        break
      }
    }
    if matched_rep >= 0 {
      rep_of[s] = matched_rep
    } else {
      rep_of[s] = s
      reps.push(s)
    }
  }

  // Step 2: Canonical BFS traversal of reachable quotient classes starting from `rep_of[aut.init_state]`:
  // Because stream automata are deterministic (`1` outgoing `tail_next` per state!), the reachable quotient
  // is a canonical lasso `0 -> 1 -> ... -> k-1 -> loop_entry`, uniquely determined up to isomorphism!
  let canon_id : Map[Int32, Int32] = Map([])
  let order : Array[Int32] = []
  let mut cur = rep_of[aut.init_state]
  while !canon_id.contains(cur) {
    let new_idx = order.length()
    canon_id[cur] = new_idx
    order.push(cur)
    cur = rep_of[aut.tail_next[cur]]
  }

  let k = order.length()
  let min_out : Array[Int32] = []
  let min_next : Array[Int32] = []
  for i = 0; i < k; i = i + 1 {
    let r = order[i]
    min_out.push(aut.head_out[r])
    let nxt_rep = rep_of[aut.tail_next[r]]
    let cid = match canon_id.get(nxt_rep) {
      Some(id) => id
      None => 0
    }
    min_next.push(cid)
  }
  { num_states: k, init_state: 0, head_out: min_out, tail_next: min_next, }
}

///|
fn encode_nat_syn(v : Int32) -> @m1.SynExpr {
  let mut acc = @m1.mk_zero()
  let mut rem = if v >= 0 { v } else { -v }
  while rem > 0 {
    acc = @m1.mk_succ(acc)
    rem = rem - 1
  }
  if v < 0 {
    @m1.mk_inl(acc, @m1.mk_nat_ty())
  } else {
    @m1.mk_inr(acc, @m1.mk_nat_ty())
  }
}

///|
/// Intern the localized quotient normal form of `aut` into M1's Hash-Consed `SyntaxArena`,
/// turning infinite-stream bisimulation into O(1) `Int32` ID comparison!
pub fn localize_coalgebra_to_arena_id(
  arena : @m1.SyntaxArena,
  aut : @m9.FiniteStreamAutomaton,
) -> Int32 raise Error {
  let min_aut = minimize_stream_coalgebra(aut)
  let mut code = @m1.mk_unit_val()
  for i = min_aut.num_states - 1; i >= 0; i = i - 1 {
    let st_pair = @m1.mk_pair(
      encode_nat_syn(min_aut.head_out[i]),
      encode_nat_syn(min_aut.tail_next[i]),
      @m1.mk_nat_ty(),
    )
    code = @m1.mk_pair(st_pair, code, @m1.mk_unit_ty())
  }
  arena.intern(code)
}

///|
/// 4. Functorial Reflection of M8 Inductive-Inductive `(IICtx, IITy)` into M3's NbE Kernel!
/// Compiles well-typed intrinsic `(IICtx, IITy)` into `(JudgmentCtx, CoreTm)` and certifies `check_is_type`!
pub fn compile_ii_ty_to_core(ty : @m8.IITy) -> @m3.CoreTm {
  match ty {
    IIBase(_, card) => if card == 1 { CUnit } else { CNat }
    IIPi(_, a, b) =>
      CPi("x", compile_ii_ty_to_core(a), compile_ii_ty_to_core(b))
    IISigma(_, a, b) =>
      CSigma("x", compile_ii_ty_to_core(a), compile_ii_ty_to_core(b))
  }
}

///|
pub fn reflect_ii_ctx_and_certify_ty(
  ctx : @m8.IICtx,
  ty : @m8.IITy,
) -> (@m3.JudgmentCtx, @m3.Val, Int32) raise Error {
  @m8.check_ii_ty(ctx, ty)
  fn build_jctx(c : @m8.IICtx) -> @m3.JudgmentCtx raise Error {
    match c {
      IINil => @m3.JudgmentCtx::empty(true)
      IISnoc(g, a) => {
        let jg = build_jctx(g)
        let ca = compile_ii_ty_to_core(a)
        let (va, _) = @m3.check_is_type(jg, ca)
        jg.push_var("v", va)
      }
    }
  }

  let jctx = build_jctx(ctx)
  let cty = compile_ii_ty_to_core(ty)
  let (vty, lvl) = @m3.check_is_type(jctx, cty)
  (jctx, vty, lvl)
}
