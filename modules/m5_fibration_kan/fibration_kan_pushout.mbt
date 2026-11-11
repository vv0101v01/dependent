///|
/// Module M5 — Categorical Combination of M1 (Syntax/Context), M2 (Universes), and M3 (Π/Σ/NbE):
/// 1. Functorial AST Bridge `SynExpr <-> CoreTm`
/// 2. Grothendieck Comprehension Fibration `p : ∫_Ctx Ty -> Ctx` & Cloven Cartesian Lifts
/// 3. Left & Right Kan Extensions (`Lan_π = Σ_π ⊣ π* ⊣ Π_π = Ran_π`)
/// 4. Context Fibered Product (Pullback in Ctx / Amalgamated Pushout of Theories in Ctx^op)
/// 5. Beck-Chevalley Commutation & Sheaf Section Gluing + Operadic Fibered Grafting.

///|
pub suberror FibrationError {
  BridgeUnsupportedConstruct(String)
  InvalidMorphismArity(Int32, Int32)
  InvalidExtensionSlice(Int32, Int32)
  IncompatibleBaseContext(Int32, Int32)
  SheafGluingRestrictionMismatch
  BeckChevalleyFailure
}

///|
/// Functorial Bridge from M1 Bit-Summary `SynExpr` to M3 Semantic Kernel `CoreTm`.
pub fn syn_to_core(e : @m1.SynExpr) -> @m3.CoreTm raise FibrationError {
  match e.kind {
    Var(i) => CVar(i)
    Univ(l) => CUniv(l)
    PolyUniv(v, off) => CPolyUniv(v, off)
    PropSort => CProp
    SmallEncode(l, a) => CSmallEnc(l, syn_to_core(a))
    SmallDecode(l, m) => CSmallDec(l, syn_to_core(m))
    Pi(x, a, b) => CPi(x, syn_to_core(a), syn_to_core(b))
    Lam(x, a, b) => CLam(x, syn_to_core(a), syn_to_core(b))
    App(f, a) => CApp(syn_to_core(f), syn_to_core(a))
    Sigma(x, a, b) => CSigma(x, syn_to_core(a), syn_to_core(b))
    Pair(a, b, m) => CPair(syn_to_core(a), syn_to_core(b), syn_to_core(m))
    Fst(p) => CFst(syn_to_core(p))
    Snd(p) => CSnd(syn_to_core(p))
    UnitTy => CUnit
    UnitVal => CStar
    NatTy => CNat
    Zero => CZero
    Succ(n) => CSucc(syn_to_core(n))
    NatRec(m, z, s, n) =>
      CNatRec(syn_to_core(m), syn_to_core(z), syn_to_core(s), syn_to_core(n))
    IdTy(t, l, r) => CId(syn_to_core(t), syn_to_core(l), syn_to_core(r))
    Refl(t, x) => CRefl(syn_to_core(t), syn_to_core(x))
    JElim(t, l, m, rf, r, p) =>
      CJ(
        syn_to_core(t),
        syn_to_core(l),
        syn_to_core(m),
        syn_to_core(rf),
        syn_to_core(r),
        syn_to_core(p),
      )
    SquashTy(a) => CSquash(syn_to_core(a))
    SquashIntro(w) => CBoxProof(syn_to_core(w))
    BoolTy => CBool
    BoolLit(b) => CBoolLit(b)
    EmptyTy => CEmpty
    Absurd(t, c) => CAbsurd(syn_to_core(t), syn_to_core(c))
    SumTy(a, b) => CSum(syn_to_core(a), syn_to_core(b))
    Inl(sty, v) => CInl(syn_to_core(sty), syn_to_core(v))
    Inr(sty, v) => CInr(syn_to_core(sty), syn_to_core(v))
    CaseSum(s, m, l, r) =>
      CCase(syn_to_core(s), syn_to_core(m), syn_to_core(l), syn_to_core(r))
    Hole(s) =>
      raise FibrationError::BridgeUnsupportedConstruct("Unfilled Hole(\{s})")
    ConstRef(_, _) =>
      raise FibrationError::BridgeUnsupportedConstruct("Opaque ConstRef")
  }
}

///|
/// Functorial Bridge from M3 `CoreTm` back into M1 Bit-Summary `SynExpr` (recomputing O(1) masks & hashes!).
pub fn core_to_syn(tm : @m3.CoreTm) -> @m1.SynExpr {
  match tm {
    CVar(i) => @m1.mk_var_unchecked(i)
    CUniv(l) => @m1.mk_univ(l)
    CPolyUniv(v, o) => @m1.mk_poly_univ(v, o)
    CProp => @m1.mk_prop_sort()
    CSmallEnc(l, a) => @m1.mk_small_encode(l, core_to_syn(a))
    CSmallDec(l, m) => @m1.mk_small_decode(l, core_to_syn(m))
    CPi(x, a, b) => @m1.mk_pi(x, core_to_syn(a), core_to_syn(b))
    CLam(x, a, b) => @m1.mk_lam(x, core_to_syn(a), core_to_syn(b))
    CApp(f, a) => @m1.mk_app(core_to_syn(f), core_to_syn(a))
    CSigma(x, a, b) => @m1.mk_sigma(x, core_to_syn(a), core_to_syn(b))
    CPair(a, b, m) =>
      @m1.mk_pair(core_to_syn(a), core_to_syn(b), core_to_syn(m))
    CFst(p) => @m1.mk_fst(core_to_syn(p))
    CSnd(p) => @m1.mk_snd(core_to_syn(p))
    CUnit => @m1.mk_unit_ty()
    CStar => @m1.mk_unit_val()
    CNat => @m1.mk_nat_ty()
    CZero => @m1.mk_zero()
    CSucc(n) => @m1.mk_succ(core_to_syn(n))
    CNatRec(m, z, s, n) =>
      @m1.mk_nat_rec(
        core_to_syn(m),
        core_to_syn(z),
        core_to_syn(s),
        core_to_syn(n),
      )
    CId(t, l, r) => @m1.mk_id_ty(core_to_syn(t), core_to_syn(l), core_to_syn(r))
    CRefl(t, x) => @m1.mk_refl(core_to_syn(t), core_to_syn(x))
    CJ(t, l, m, rf, r, p) =>
      @m1.mk_j_elim(
        core_to_syn(t),
        core_to_syn(l),
        core_to_syn(m),
        core_to_syn(rf),
        core_to_syn(r),
        core_to_syn(p),
      )
    CSquash(a) => @m1.mk_squash_ty(core_to_syn(a))
    CBoxProof(w) => @m1.mk_squash_intro(core_to_syn(w))
    CBool => @m1.mk_bool_ty()
    CBoolLit(b) => @m1.mk_bool_lit(b)
    CEmpty => @m1.mk_empty_ty()
    CAbsurd(t, c) => @m1.mk_absurd(core_to_syn(t), core_to_syn(c))
    CSum(a, b) => @m1.mk_sum_ty(core_to_syn(a), core_to_syn(b))
    CInl(sty, v) => @m1.mk_inl(core_to_syn(sty), core_to_syn(v))
    CInr(sty, v) => @m1.mk_inr(core_to_syn(sty), core_to_syn(v))
    CCase(s, m, l, r) =>
      @m1.mk_case_sum(
        core_to_syn(s),
        core_to_syn(m),
        core_to_syn(l),
        core_to_syn(r),
      )
    CAnn(e, _) => core_to_syn(e)
  }
}

///|
/// Reflect an M1 `Context` into an M3 semantic `JudgmentCtx` for NbE & Bidirectional Typechecking.
pub fn reflect_ctx_to_m3(
  ctx : @m1.Context,
  allow_cumul : Bool,
) -> @m3.JudgmentCtx raise Error {
  let mut jctx = @m3.JudgmentCtx::empty(allow_cumul)
  for entry in ctx.entries {
    let core_ty = syn_to_core(entry.ty)
    let (vty, _) = @m3.check_is_type(jctx, core_ty)
    match entry.local_def {
      None => jctx = jctx.push_var(entry.name, vty)
      // Zeta-binders reflect as DEFINITION VALUES: every later reference to `name`
      // zeta-expands to `v` inside the NbE kernel (e.g. `x : Nat := 0` reflects so
      // that `x` normalizes to `0`).
      Some(v) => {
        let core_v = syn_to_core(v)
        @m3.check_term(jctx, core_v, vty)
        let vval = @m3.eval_tm(jctx.env, core_v)
        jctx = jctx.push_def(entry.name, vty, vval)
      }
    }
  }
  jctx
}

///|
/// Object of the Grothendieck Total Category `∫_Ctx Ty`:
/// Pairs a base context `Γ` with a fiber type `A` over `Γ` and its algebraic universe smallness rank!
#derive(Eq, Debug)
pub(all) struct FibredType {
  base : @m1.Context
  fiber_ty : @m1.SynExpr
  smallness : @m2.AlgLevel
}

///|
pub extend FibredType with Eq::{equal, not_equal}

///|
pub extend FibredType with @debug.Debug::{to_repr}

///|
/// Context Morphism `σ : dom -> cod` in the Base Category `Ctx`:
/// Assigns to each level `0 <= l < |cod|` a term `terms_by_lvl[l]` scoped in `dom`.
#derive(Eq, Debug)
pub(all) struct CtxMorphism {
  dom : @m1.Context
  cod : @m1.Context
  terms_by_lvl : Array[@m1.SynExpr]
}

///|
pub extend CtxMorphism with Eq::{equal, not_equal}

///|
pub extend CtxMorphism with @debug.Debug::{to_repr}

///|
/// Identity Context Morphism `id_Γ : Γ -> Γ`.
pub fn id_ctx_morphism(ctx : @m1.Context) -> CtxMorphism {
  let d = ctx.len()
  let terms : Array[@m1.SynExpr] = []
  for lvl = 0; lvl < d; lvl = lvl + 1 {
    let idx = d - 1 - lvl
    terms.push(@m1.mk_var_unchecked(idx))
  }
  { dom: ctx, cod: ctx, terms_by_lvl: terms, }
}

///|
/// Display Projection Morphism `π_drop : (Γ, Δ_drop) -> Γ` forgetting the last `drop_count` hypotheses!
pub fn display_projection_morphism(
  extended_ctx : @m1.Context,
  drop_count : Int32,
) -> CtxMorphism raise FibrationError {
  let n = extended_ctx.len()
  if drop_count < 0 || drop_count > n {
    raise FibrationError::InvalidExtensionSlice(drop_count, n)
  }
  let keep = n - drop_count
  let mut base = @m1.Context::empty()
  for i = 0; i < keep; i = i + 1 {
    let e = extended_ctx.entries[i]
    base = base.extend_var(e.name, e.ty)
  }
  let terms : Array[@m1.SynExpr] = []
  for lvl = 0; lvl < keep; lvl = lvl + 1 {
    let idx_in_ext = n - 1 - lvl
    terms.push(@m1.mk_var_unchecked(idx_in_ext))
  }
  { dom: extended_ctx, cod: base, terms_by_lvl: terms, }
}

///|
/// Convert `CtxMorphism` `σ : dom -> cod` into M1's `Subst` mapping De Bruijn indices of `cod` to terms in `dom`.
pub fn morphism_to_subst(mor : CtxMorphism) -> @m1.Subst raise FibrationError {
  let m = mor.cod.len()
  if mor.terms_by_lvl.length() != m {
    raise FibrationError::InvalidMorphismArity(mor.terms_by_lvl.length(), m)
  }
  // De Bruijn index 0 in `cod` corresponds to level `m - 1`, index `m - 1` to level `0`:
  let mut acc = @m1.subst_shift(mor.dom.len())
  for lvl = 0; lvl < m; lvl = lvl + 1 {
    acc = @m1.subst_cons(mor.terms_by_lvl[lvl], acc)
  }
  acc
}

///|
/// Compose Context Morphisms `(g ∘ f) : A -> C` for `f : A -> B` and `g : B -> C` in `Ctx`!
pub fn compose_ctx_morphisms(
  f : CtxMorphism,
  g : CtxMorphism,
) -> CtxMorphism raise FibrationError {
  if f.cod != g.dom {
    raise FibrationError::IncompatibleBaseContext(f.cod.len(), g.dom.len())
  }
  let f_sub = morphism_to_subst(f)
  let comp_terms : Array[@m1.SynExpr] = []
  for t in g.terms_by_lvl {
    comp_terms.push(@m1.apply_subst(t, f_sub))
  }
  { dom: f.dom, cod: g.cod, terms_by_lvl: comp_terms, }
}

///|
/// Cloven Cartesian Lift / Pullback Reindexing Functor `mor*(fib)` in the Grothendieck Fibration `∫_Ctx Ty -> Ctx`:
/// Pulls `fib` over `cod` back along `mor : dom -> cod` to a `FibredType` over `dom`, preserving smallness!
pub fn cartesian_reindex(
  mor : CtxMorphism,
  fib : FibredType,
) -> FibredType raise FibrationError {
  if mor.cod != fib.base {
    raise FibrationError::IncompatibleBaseContext(mor.cod.len(), fib.base.len())
  }
  let sub = morphism_to_subst(mor)
  {
    base: mor.dom,
    fiber_ty: @m1.apply_subst(fib.fiber_ty, sub),
    smallness: fib.smallness,
  }
}

///|
/// Synthesize algebraic universe smallness for an M1 `SynExpr` inside `FibredType`.
pub fn estimate_syn_smallness(e : @m1.SynExpr) -> @m2.AlgLevel {
  match e.kind {
    Univ(i) => @m2.AlgLevel::concrete_clamped(i + 1)
    PolyUniv(v, off) => @m2.AlgLevel::normalize(off + 1, [(v, off + 1)])
    PropSort | UnitTy | EmptyTy | NatTy | SquashTy(_) => @m2.AlgLevel::zero()
    SmallDecode(i, _) => @m2.AlgLevel::concrete_clamped(i)
    Pi(_, a, b) | Sigma(_, a, b) | SumTy(a, b) =>
      estimate_syn_smallness(a).lub(estimate_syn_smallness(b))
    IdTy(t, _, _) => estimate_syn_smallness(t)
    _ => @m2.AlgLevel::zero()
  }
}

///|
/// Left Kan Extension `Lan_π (Σ_π)` along `ext_len`-step Display Projection `π : (Γ, Δ) -> Γ`:
/// Maps `fib` over `(Γ, Δ)` to `Σ(x_1 : D_1). ... Σ(x_r : D_r). A` over `Γ`!
pub fn left_kan_sigma(
  ext_len : Int32,
  fib : FibredType,
) -> FibredType raise FibrationError {
  let n = fib.base.len()
  if ext_len < 0 || ext_len > n {
    raise FibrationError::InvalidExtensionSlice(ext_len, n)
  }
  let mut cur_ty = fib.fiber_ty
  let mut cur_small = fib.smallness
  for step = 0; step < ext_len; step = step + 1 {
    let idx = n - 1 - step
    let entry = fib.base.entries[idx]
    cur_ty = @m1.mk_sigma(entry.name, entry.ty, cur_ty)
    cur_small = cur_small.lub(estimate_syn_smallness(entry.ty))
  }
  let keep = n - ext_len
  let mut out_base = @m1.Context::empty()
  for i = 0; i < keep; i = i + 1 {
    let e = fib.base.entries[i]
    out_base = out_base.extend_var(e.name, e.ty)
  }
  { base: out_base, fiber_ty: cur_ty, smallness: cur_small, }
}

///|
/// Right Kan Extension `Ran_π (Π_π)` along `ext_len`-step Display Projection `π : (Γ, Δ) -> Γ`:
/// Maps `fib` over `(Γ, Δ)` to `Π(x_1 : D_1). ... Π(x_r : D_r). A` over `Γ`!
pub fn right_kan_pi(
  ext_len : Int32,
  fib : FibredType,
) -> FibredType raise FibrationError {
  let n = fib.base.len()
  if ext_len < 0 || ext_len > n {
    raise FibrationError::InvalidExtensionSlice(ext_len, n)
  }
  let mut cur_ty = fib.fiber_ty
  let mut cur_small = fib.smallness
  for step = 0; step < ext_len; step = step + 1 {
    let idx = n - 1 - step
    let entry = fib.base.entries[idx]
    cur_ty = @m1.mk_pi(entry.name, entry.ty, cur_ty)
    cur_small = cur_small.lub(estimate_syn_smallness(entry.ty))
  }
  let keep = n - ext_len
  let mut out_base = @m1.Context::empty()
  for i = 0; i < keep; i = i + 1 {
    let e = fib.base.entries[i]
    out_base = out_base.extend_var(e.name, e.ty)
  }
  { base: out_base, fiber_ty: cur_ty, smallness: cur_small, }
}

///|
/// Context Pullback Square in `Ctx` (= Amalgamated Theory Pushout `Γ_1 ⊔_{Γ_0} Γ_2` in `Ctx^op`):
/// Given `Γ_1 = (Γ_0, Δ_1)` and `Γ_2 = (Γ_0, Δ_2)` sharing prefix `Γ_0` of length `base_len`,
/// builds `apex = (Γ_0, Δ_1, weaken(Δ_2))` together with projections `proj1 : apex -> Γ_1` and `proj2 : apex -> Γ_2`!
#derive(Eq, Debug)
pub(all) struct ContextPullbackSquare {
  base_len : Int32
  apex : @m1.Context
  proj1 : CtxMorphism
  proj2 : CtxMorphism
}

///|
pub extend ContextPullbackSquare with Eq::{equal, not_equal}

///|
pub extend ContextPullbackSquare with @debug.Debug::{to_repr}

///|
pub fn build_context_pullback(
  base_len : Int32,
  ctx1 : @m1.Context,
  ctx2 : @m1.Context,
) -> ContextPullbackSquare raise FibrationError {
  if base_len < 0 || base_len > ctx1.len() || base_len > ctx2.len() {
    raise FibrationError::InvalidExtensionSlice(base_len, ctx1.len())
  }
  for i = 0; i < base_len; i = i + 1 {
    if ctx1.entries[i].ty != ctx2.entries[i].ty {
      raise FibrationError::IncompatibleBaseContext(base_len, i)
    }
  }
  let len1_ext = ctx1.len() - base_len
  let len2_ext = ctx2.len() - base_len
  let mut apex = ctx1
  // Append `Δ_2`, shifting references across `Δ_1` (inserted at cutoff `i - base_len`):
  for i = base_len; i < ctx2.len(); i = i + 1 {
    let e2 = ctx2.entries[i]
    let local_offset = i - base_len
    let shifted_ty = @m1.shift_expr_simple(e2.ty, len1_ext, local_offset)
    apex = apex.extend_var(e2.name, shifted_ty)
  }
  let total_len = apex.len()
  // `proj1 : apex -> ctx1` maps levels `0 .. ctx1.len()-1` directly to levels `0 .. ctx1.len()-1` in `apex`:
  let p1_terms : Array[@m1.SynExpr] = []
  for lvl = 0; lvl < ctx1.len(); lvl = lvl + 1 {
    p1_terms.push(@m1.mk_var_unchecked(total_len - 1 - lvl))
  }
  // `proj2 : apex -> ctx2` maps `0 .. base_len-1` to `0 .. base_len-1`, and `base_len + k` to `ctx1.len() + k`!
  let p2_terms : Array[@m1.SynExpr] = []
  for lvl = 0; lvl < base_len; lvl = lvl + 1 {
    p2_terms.push(@m1.mk_var_unchecked(total_len - 1 - lvl))
  }
  for k = 0; k < len2_ext; k = k + 1 {
    let apex_lvl = ctx1.len() + k
    p2_terms.push(@m1.mk_var_unchecked(total_len - 1 - apex_lvl))
  }
  {
    base_len,
    apex,
    proj1: { dom: apex, cod: ctx1, terms_by_lvl: p1_terms, },
    proj2: { dom: apex, cod: ctx2, terms_by_lvl: p2_terms, },
  }
}

///|
/// Theorem 5.1 (Beck-Chevalley Natural Isomorphism Verification on Pullback Squares):
/// Given `fib_over_ctx2` over `ctx2 = (Γ_0, Δ_2)` and `sq = build_context_pullback(base_len, ctx1, ctx2)`:
/// Verifies via M3's NbE kernel that:
///   1. `π_1*(Lan_{π_2}(A)) ≡ Lan_{proj1}(proj2*(A))`  (Σ Beck-Chevalley!)
///   2. `π_1*(Ran_{π_2}(A)) ≡ Ran_{proj1}(proj2*(A))`  (Π Beck-Chevalley!)
pub fn verify_beck_chevalley(
  sq : ContextPullbackSquare,
  fib_over_ctx2 : FibredType,
) -> Bool raise Error {
  let ctx1 = sq.proj1.cod
  let ctx2 = sq.proj2.cod
  let ext1_len = ctx1.len() - sq.base_len
  let ext2_len = ctx2.len() - sq.base_len
  let pi1 = display_projection_morphism(ctx1, ext1_len)

  // Path A (Down then Pullback): Lan_{π_2}(A) over Γ_0, then reindex along π_1 : ctx1 -> Γ_0
  let lan_down = left_kan_sigma(ext2_len, fib_over_ctx2)
  let lhs_sigma = cartesian_reindex(pi1, lan_down)

  // Path B (Pullback to Apex then Down along proj1): proj2*(A) over apex, then Lan along ext2_len
  let pulled_to_apex = cartesian_reindex(sq.proj2, fib_over_ctx2)
  let rhs_sigma = left_kan_sigma(ext2_len, pulled_to_apex)

  // Similarly for Right Kan Extension (Π):
  let ran_down = right_kan_pi(ext2_len, fib_over_ctx2)
  let lhs_pi = cartesian_reindex(pi1, ran_down)
  let rhs_pi = right_kan_pi(ext2_len, pulled_to_apex)

  let jctx1 = reflect_ctx_to_m3(ctx1, true)
  let d = jctx1.depth()
  let sig_ok = @m3.conv_ty(
    d,
    @m3.eval_tm(jctx1.env, syn_to_core(lhs_sigma.fiber_ty)),
    @m3.eval_tm(jctx1.env, syn_to_core(rhs_sigma.fiber_ty)),
  )
  let pi_ok = @m3.conv_ty(
    d,
    @m3.eval_tm(jctx1.env, syn_to_core(lhs_pi.fiber_ty)),
    @m3.eval_tm(jctx1.env, syn_to_core(rhs_pi.fiber_ty)),
  )
  if !(sig_ok && pi_ok) {
    raise FibrationError::BeckChevalleyFailure
  }
  true
}

///|
/// Sheaf Gluing / Compatible Family Amalgamation over Context Cover (`組合範例.md` #2 & #3):
/// Given local terms `s1` over `ctx1` (of type `π_1* T_0`) and `s2` over `ctx2` (of type `π_2* T_0`),
/// together with base specialization morphism `anchor1 : Γ_0 -> ctx1` and `anchor2 : Γ_0 -> ctx2`,
/// checks agreement `anchor1*(s1) ≡ anchor2*(s2) : T_0` via M3 NbE and glues `(proj1* s1, proj2* s2)`
/// into a certified pair on `apex = ctx1 ×_{Γ_0} ctx2`!
pub fn glue_compatible_local_terms(
  sq : ContextPullbackSquare,
  base_ctx : @m1.Context,
  base_ty : @m1.SynExpr,
  anchor1 : CtxMorphism,
  anchor2 : CtxMorphism,
  s1 : @m1.SynExpr,
  s2 : @m1.SynExpr,
) -> @m1.SynExpr raise Error {
  let sub_a1 = morphism_to_subst(anchor1)
  let sub_a2 = morphism_to_subst(anchor2)
  let r1 = @m1.apply_subst(s1, sub_a1)
  let r2 = @m1.apply_subst(s2, sub_a2)
  let jbase = reflect_ctx_to_m3(base_ctx, true)
  let vty = @m3.eval_tm(jbase.env, syn_to_core(base_ty))
  let vr1 = @m3.eval_tm(jbase.env, syn_to_core(r1))
  let vr2 = @m3.eval_tm(jbase.env, syn_to_core(r2))
  if !@m3.conv_val(jbase.depth(), vty, vr1, vr2) {
    raise FibrationError::SheafGluingRestrictionMismatch
  }
  let p1_s1 = @m1.apply_subst(s1, morphism_to_subst(sq.proj1))
  let p2_s2 = @m1.apply_subst(s2, morphism_to_subst(sq.proj2))
  let apex_ty = @m1.shift_expr_simple(base_ty, sq.apex.len() - sq.base_len, 0)
  @m1.mk_pair(p1_s1, p2_s2, @m1.shift_expr_simple(apex_ty, 1, 0))
}

///|
/// Operadic Fibered Derivation Grafting (`組合範例.md` #9):
/// Grafts typed fibered premises `(slot_id, premise_term)` into an open `host_template` over `ctx`,
/// then verifies the grafted term against `expected_ty` in M3's bidirectional NbE kernel!
pub fn graft_and_verify_fibered_operad(
  ctx : @m1.Context,
  host_template : @m1.SynExpr,
  plugs : Array[(Int32, @m1.SynExpr)],
  expected_ty : @m1.SynExpr,
  allow_cumul : Bool,
) -> @m3.CoreTm raise Error {
  let grafted = @m1.operad_graft(host_template, plugs)
  let jctx = reflect_ctx_to_m3(ctx, allow_cumul)
  let core_tm = syn_to_core(grafted)
  let core_ty = syn_to_core(expected_ty)
  let (v_exp, _) = @m3.check_is_type(jctx, core_ty)
  @m3.check_term(jctx, core_tm, v_exp)
  @m3.quote_val(jctx.depth(), v_exp, @m3.eval_tm(jctx.env, core_tm))
}
