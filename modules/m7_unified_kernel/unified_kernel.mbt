///|
/// Module M7 — Grand Unified Dependent Type Theory Kernel:
/// Integrates M1 (Bit-Mask Syntax, σ-Calculus, Matroid Contexts, Arena),
/// M2 (Algebraic & Fuss-Free Cumulative Universes, Galois Constraint Graph, Ramsey/Dilworth),
/// M3 (Π/Σ Bidirectional Kernel, Typed-Neutral Kripke NbE, Currying & Skolem Choice),
/// M4 (Curry-Howard Bijection, Sequent Cut-Elimination, CPS Classical Embedding, Proof Erasure),
/// M5 (Grothendieck Comprehension Fibration, Kan Extensions, Pullback/Pushout, Beck-Chevalley, Sheaf Gluing),
/// M6 (64-Bit Chu Spaces, Galois Correspondence, Logic->DTT Compiler, Morita, Localization, Games),
/// plus Semidirect Context Action Products (`組合範例.md` #8) & Telescope Short Exact Sequences (`組合範例.md` #13)!

///|
pub(all) suberror KernelError {
  UniverseInconsistency(String)
  DeclarationLevelInsufficient(Int32, Int32)
  InvalidPermutation(Int32)
  DependencyViolatingSwap(Int32, Int32)
  NonSplitExactSequence(Int32)
  /// `base_len` of a telescope short exact sequence must satisfy `0 <= base_len <= |total_ctx|`.
  InvalidBaseLength(Int32, Int32)
  /// Every fiber hypothesis of a splitting section needs exactly one closed default witness.
  FiberDefaultCountMismatch(Int32, Int32)
  /// A fiber default witness must be a CLOSED term (it lives over `Γ_base` alone).
  NonClosedFiberDefault(Int32)
}

///|
/// Certified Kernel Theorem / Declaration Artifact.
#derive(Eq, Debug)
pub(all) struct CertifiedArtifact {
  name : String
  arena_type_id : Int32
  arena_term_id : Int32
  inferred_univ_level : Int32
  normal_form : @m3.CoreTm
  extracted_witness : @m4.ExtractedProg?
}

///|
pub extend CertifiedArtifact with Eq::{equal, not_equal}

///|
pub extend CertifiedArtifact with @debug.Debug::{to_repr}

///|
/// Unified Kernel Statistical & Structural Telemetry.
#derive(Eq, Debug)
pub(all) struct KernelTelemetry {
  arena_unique_nodes : Int32
  context_depth : Int32
  universe_var_count : Int32
  universe_longest_chain : Int32
  universe_max_antichain : Int32
  certified_artifacts : Int32
  galois_law_verified : Bool
  beck_chevalley_verified : Bool
}

///|
pub extend KernelTelemetry with Eq::{equal, not_equal}

///|
pub extend KernelTelemetry with @debug.Debug::{to_repr}

///|
/// Unified Dependent Type Theory Kernel State.
pub struct UnifiedKernel {
  arena : @m1.SyntaxArena
  mut ctx : @m1.Context
  ugraph : @m2.UniverseGraph
  mode : @m2.HierarchyMode
  artifacts : Array[CertifiedArtifact]
}

///|
pub fn UnifiedKernel::new(mode : @m2.HierarchyMode) -> UnifiedKernel {
  {
    arena: @m1.SyntaxArena::new(),
    ctx: @m1.Context::empty(),
    ugraph: @m2.UniverseGraph::new(0),
    mode,
    artifacts: [],
  }
}

///|
fn UnifiedKernel::allow_cumul(self : UnifiedKernel) -> Bool {
  match self.mode {
    Cumulative => true
    NonCumulative => false
  }
}

///|
/// Extend the global kernel context with a verified type `x : ty`!
pub fn UnifiedKernel::assume_variable(
  self : UnifiedKernel,
  name : String,
  ty : @m1.SynExpr,
) -> Int32 raise Error {
  let jctx = @m5.reflect_ctx_to_m3(self.ctx, self.allow_cumul())
  let core_ty = @m5.syn_to_core(ty)
  let (_, lvl) = @m3.check_is_type(jctx, core_ty)
  let uvar = self.ugraph.fresh_var()
  self.ugraph.add_const_floor(lvl, uvar)
  if !self.ugraph.is_consistent() {
    raise KernelError::UniverseInconsistency(name)
  }
  let _ = self.arena.intern(ty)
  self.ctx = self.ctx.extend_var(name, ty)
  lvl
}

///|
/// Certify a full Dependent Type Theory Definition / Theorem `(name : syn_ty := syn_tm)`
/// against declared universe ceiling `declared_univ`, interning in M1's DAG Arena,
/// checking universe admissibility in M2's Galois Graph, and normalizing in M3's NbE Kernel!
pub fn UnifiedKernel::certify_dtt_theorem(
  self : UnifiedKernel,
  name : String,
  syn_ty : @m1.SynExpr,
  syn_tm : @m1.SynExpr,
  declared_univ : Int32,
) -> CertifiedArtifact raise Error {
  let ty_id = self.arena.intern(syn_ty)
  let tm_id = self.arena.intern(syn_tm)
  let jctx = @m5.reflect_ctx_to_m3(self.ctx, self.allow_cumul())
  let core_ty = @m5.syn_to_core(syn_ty)
  let core_tm = @m5.syn_to_core(syn_tm)
  let (vty, min_lvl) = @m3.check_is_type(jctx, core_ty)
  // Verify level relationship in M2 according to `self.mode` (`Cumulative` vs `NonCumulative`)!
  self.ugraph.check_level_rel(
    self.mode,
    Covariant,
    @m2.AlgLevel::concrete_clamped(min_lvl),
    @m2.AlgLevel::concrete_clamped(declared_univ),
  ) catch {
    _ => raise KernelError::DeclarationLevelInsufficient(min_lvl, declared_univ)
  }
  let uvar = self.ugraph.fresh_var()
  self.ugraph.add_const_floor(min_lvl, uvar)
  self.ugraph.add_const_ceiling(uvar, declared_univ)
  if !self.ugraph.is_consistent() {
    raise KernelError::UniverseInconsistency(name)
  }
  @m3.check_term(jctx, core_tm, vty)
  let nf = @m3.quote_val(jctx.depth(), vty, @m3.eval_tm(jctx.env, core_tm))
  let art : CertifiedArtifact = {
    name,
    arena_type_id: ty_id,
    arena_term_id: tm_id,
    inferred_univ_level: min_lvl,
    normal_form: nf,
    extracted_witness: None,
  }
  self.artifacts.push(art)
  art
}

///|
/// End-to-End Curry-Howard + Sequent Cut-Elimination + Witness Extraction + DTT Kernel Certification!
/// Takes a constructive proof `prf` of an M4 `CHType` (e.g., `∀x:Nat. ∃y:Nat. ...` or a cut-eliminated sequent):
/// 1. Infers `CHType` in M4 (`infer_ch_term`),
/// 2. Normalizes detours in M4 (`normalize_ch_term`) AND extracts pure program (`extract_computational_program`),
/// 3. Compiles BOTH type and proof via M6's Dual-Namespace Bridge into M3 `CoreTm`,
/// 4. Reflects via M5 into M1 `SynExpr` (computing 64-bit bitmasks & interning in `SyntaxArena`),
/// 5. Re-checks the compiled proof from scratch inside M3's Dependent Type Theory NbE Kernel!
pub fn UnifiedKernel::certify_curry_howard_proof(
  self : UnifiedKernel,
  name : String,
  prf : @m4.CHTerm,
) -> CertifiedArtifact raise Error {
  let ch_ty = @m4.infer_ch_term([], prf)
  let norm_prf = @m4.normalize_ch_term(prf)
  let witness = @m4.extract_computational_program([], norm_prf)
  let core_ty = @m6.compile_ch_type_to_core([], ch_ty)
  let core_tm = @m6.compile_ch_term_to_core([], norm_prf)
  let syn_ty = @m5.core_to_syn(core_ty)
  let syn_tm = @m5.core_to_syn(core_tm)
  let ty_id = self.arena.intern(syn_ty)
  let tm_id = self.arena.intern(syn_tm)

  let j0 = @m3.JudgmentCtx::empty(self.allow_cumul())
  let (vty, min_lvl) = @m3.check_is_type(j0, core_ty)
  @m3.check_term(j0, core_tm, vty)
  let nf = @m3.quote_val(0, vty, @m3.eval_tm(j0.env, core_tm))
  let uvar = self.ugraph.fresh_var()
  self.ugraph.add_const_floor(min_lvl, uvar)
  let art : CertifiedArtifact = {
    name,
    arena_type_id: ty_id,
    arena_term_id: tm_id,
    inferred_univ_level: min_lvl,
    normal_form: nf,
    extracted_witness: Some(witness),
  }
  self.artifacts.push(art)
  art
}

///|
/// ============================================================================
/// Semidirect / Crossed Product of Context Renaming Automorphisms & Fibered Substitutions
/// (`組合範例.md` #8): `G = Subst(n) ⋊ Sym_adm(n)`
/// ============================================================================
/// An element `(perm, fiber_terms)` acts on expressions over an `n`-variable independent context block:
/// - `perm` is a bijection on `{0 .. n-1}` (level `l` moves to level `perm[l]`),
/// - `fiber_terms[l]` refines variable at level `l` AFTER permutation!
/// Groupoid/Monoid Semidirect Multiplication:
/// `(p2, t2) ⋊ (p1, t1) = (p2 ∘ p1,  l |-> apply_subst(t1[l], sub(t2 ∘ p2)))`!
#derive(Eq, Debug)
pub(all) struct SemidirectCtxElem {
  arity : Int32
  perm : Array[Int32]
  fiber_terms : Array[@m1.SynExpr]
}

///|
pub extend SemidirectCtxElem with Eq::{equal, not_equal}

///|
pub extend SemidirectCtxElem with @debug.Debug::{to_repr}

///|
/// Exact free-occurrence test delegating to M1's intrinsic bit-summary + exact
/// slow-path fallback (replaces the former conservative `idx >= 64` over-approximation).
fn syn_may_occur(e : @m1.SynExpr, idx : Int32) -> Bool {
  e.has_free_var(idx)
}

///|
/// Verify that `perm` is a valid bijection on `{0..n-1}` AND respects M1's Antimatroid Dependency Poset
/// (`dep_closure_mask(ctx, l)` only references levels mapped BEFORE `perm[l]`)!
pub fn verify_admissible_context_automorphism(
  ctx : @m1.Context,
  perm : Array[Int32],
) -> Bool raise KernelError {
  let n = ctx.len()
  if perm.length() != n {
    raise KernelError::InvalidPermutation(perm.length())
  }
  let seen : Array[Bool] = Array::make(n, false)
  for l = 0; l < n; l = l + 1 {
    let img = perm[l]
    if img < 0 || img >= n || seen[img] {
      raise KernelError::InvalidPermutation(img)
    }
    seen[img] = true
  }
  // Check antimatroid order preservation: if level `l` depends on level `d < l`, we must have `perm[d] < perm[l]`!
  for l = 0; l < n; l = l + 1 {
    let e_ty = ctx.entries[l].ty
    for d = 0; d < l; d = d + 1 {
      let db_idx = l - 1 - d
      if syn_may_occur(e_ty, db_idx) && perm[d] >= perm[l] {
        raise KernelError::DependencyViolatingSwap(d, l)
      }
    }
  }
  true
}

///|
/// Convert a `SemidirectCtxElem` into its induced M1 `Subst` on `n`-variable terms!
pub fn semidirect_to_subst(elem : SemidirectCtxElem) -> @m1.Subst {
  let n = elem.arity
  // First apply `perm` (level `l` -> var at level `perm[l]`, which is De Bruijn index `n - 1 - perm[l]`),
  // then substitute with `fiber_terms`:
  // Concretely, level `l` is mapped to `apply_subst(fiber_terms[perm[l]], id)`!
  let mut acc = @m1.subst_shift(n)
  for l = 0; l < n; l = l + 1 {
    let target_lvl = elem.perm[l]
    acc = @m1.subst_cons(elem.fiber_terms[target_lvl], acc)
  }
  acc
}

///|
/// Semidirect Product Composition `compose_semidirect(g2, g1)` (`g2` applied AFTER `g1` on terms:
/// `apply_subst(apply_subst(e, g1), g2) == apply_subst(e, compose_semidirect(g2, g1))`)!
pub fn compose_semidirect(
  g2 : SemidirectCtxElem,
  g1 : SemidirectCtxElem,
) -> SemidirectCtxElem raise KernelError {
  if g1.arity != g2.arity {
    raise KernelError::InvalidPermutation(g2.arity)
  }
  let n = g1.arity
  let sub2 = semidirect_to_subst(g2)
  // Notice: `g1` sends original level `l` to `g1.fiber_terms[g1.perm[l]]`.
  // Applying `sub2` afterward sends that to `apply_subst(g1.fiber_terms[g1.perm[l]], sub2)`.
  // Written in normal form `(id_perm_or_comp, new_terms)` with composed permutation `p12[l] = g2.perm[g1.perm[l]]`:
  let p12 : Array[Int32] = Array::make(n, 0)
  let inv_p2 : Array[Int32] = Array::make(n, 0)
  for i = 0; i < n; i = i + 1 {
    p12[i] = g2.perm[g1.perm[i]]
    inv_p2[g2.perm[i]] = i
  }
  // We want `new_terms[p12[l]] == apply_subst(g1.fiber_terms[g1.perm[l]], sub2)`.
  // Setting `k = g1.perm[l]`, `p12[l] = g2.perm[k]`, so for each `m = g2.perm[k]` (`k = inv_p2[m]`):
  let new_terms : Array[@m1.SynExpr] = []
  for m = 0; m < n; m = m + 1 {
    let k = inv_p2[m]
    new_terms.push(@m1.apply_subst(g1.fiber_terms[k], sub2))
  }
  { arity: n, perm: p12, fiber_terms: new_terms, }
}

///|
/// ============================================================================
/// Short Exact Sequence of Telescope Extensions & Derived Splitting Obstruction
/// (`組合範例.md` #13):  `0 -> Δ_fiber --ι--> (Γ_base . Δ_fiber) --π--> Γ_base -> 0`
/// ============================================================================
/// Measures how many fiber hypotheses in `Δ_fiber` genuinely depend on `Γ_base`!
/// Theorem 7.2 (Telescope Exact Sequence Splitting Criterion):
/// `obstruction_rank == 0` iff every fiber hypothesis in `Δ_fiber` strengthens cleanly across `Γ_base`,
/// in which case `0 -> Δ_fiber -> Γ_base.Δ_fiber -> Γ_base -> 0` SPLITS as a direct product `Γ_base × Δ_fiber`!
#derive(Eq, Debug)
pub(all) struct TelescopeExactAnalysis {
  base_len : Int32
  fiber_len : Int32
  obstruction_rank : Int32
  splits_directly : Bool
  strengthened_fiber : Array[@m1.SynExpr]
}

///|
pub extend TelescopeExactAnalysis with Eq::{equal, not_equal}

///|
pub extend TelescopeExactAnalysis with @debug.Debug::{to_repr}

///|
pub fn analyze_telescope_exact_sequence(
  total_ctx : @m1.Context,
  base_len : Int32,
) -> TelescopeExactAnalysis raise KernelError {
  let n = total_ctx.len()
  if base_len < 0 || base_len > n {
    raise KernelError::InvalidBaseLength(base_len, n)
  }
  let fiber_len = n - base_len
  let mut obs = 0
  let strengthened : Array[@m1.SynExpr] = []
  for k = 0; k < fiber_len; k = k + 1 {
    let idx_in_total = base_len + k
    let f_ty = total_ctx.entries[idx_in_total].ty
    // In `f_ty`, indices `0 .. k-1` refer to earlier fiber variables in `Δ_fiber`,
    // while indices `k .. k + base_len - 1` refer to `Γ_base`!
    // Check if `f_ty` can be strengthened by dropping `base_len` variables at cutoff `k`!
    let mut depends_on_base = false
    for b = 0; b < base_len; b = b + 1 {
      if syn_may_occur(f_ty, k + b) {
        depends_on_base = true
      }
    }
    if depends_on_base {
      obs = obs + 1
      strengthened.push(f_ty)
    } else {
      strengthened.push(@m1.shift_expr_simple(f_ty, -base_len, k + base_len))
    }
  }
  {
    base_len,
    fiber_len,
    obstruction_rank: obs,
    splits_directly: obs == 0,
    strengthened_fiber: strengthened,
  }
}

///|
/// Synthesize the Splitting Section Morphism `s : Γ_base -> (Γ_base . Δ_fiber)` when `obstruction_rank == 0`
/// given closed fiber witness terms `closed_fiber_defaults` in `Δ_fiber`, and verify `π ∘ s == id_{Γ_base}`!
pub fn synthesize_splitting_section(
  total_ctx : @m1.Context,
  base_len : Int32,
  closed_fiber_defaults : Array[@m1.SynExpr],
) -> @m5.CtxMorphism raise Error {
  let analysis = analyze_telescope_exact_sequence(total_ctx, base_len)
  if !analysis.splits_directly {
    raise KernelError::NonSplitExactSequence(analysis.obstruction_rank)
  }
  // EVERY fiber hypothesis must receive exactly one default witness, and each
  // witness must be a closed term (valid over `Γ_base` alone).
  if closed_fiber_defaults.length() != analysis.fiber_len {
    raise KernelError::FiberDefaultCountMismatch(
      closed_fiber_defaults.length(),
      analysis.fiber_len,
    )
  }
  for k, def_tm in closed_fiber_defaults {
    if !def_tm.is_closed() {
      raise KernelError::NonClosedFiberDefault(k)
    }
  }
  let mut base_ctx = @m1.Context::empty()
  for i = 0; i < base_len; i = i + 1 {
    let e = total_ctx.entries[i]
    base_ctx = base_ctx.extend_var(e.name, e.ty)
  }
  let terms : Array[@m1.SynExpr] = []
  for lvl = 0; lvl < base_len; lvl = lvl + 1 {
    terms.push(@m1.mk_var_unchecked(base_len - 1 - lvl))
  }
  for def_tm in closed_fiber_defaults {
    terms.push(@m1.shift_expr_simple(def_tm, base_len, 0))
  }
  { dom: base_ctx, cod: total_ctx, terms_by_lvl: terms, }
}

///|
/// Generate comprehensive Kernel Telemetry running M2 Ramsey-Dilworth Stratification,
/// M5 Beck-Chevalley verification, and M6 Chu-Galois verification!
pub fn UnifiedKernel::collect_telemetry(
  self : UnifiedKernel,
) -> KernelTelemetry raise Error {
  let strat = self.ugraph.stratify_ramsey_dilworth()
  // Quick Chu-Galois health check on core judgments:
  let j0 = @m3.JudgmentCtx::empty(self.allow_cumul())
  let chu = @m6.build_dtt_chu_space(j0, [CZero, CStar, CNat], [
    CNat,
    CUnit,
    CUniv(0),
  ])
  let galois_ok = chu.verify_galois_adjointness(5UL, 3UL) &&
    @m6.chu_dual(@m6.chu_dual(chu)) == chu

  // Quick Beck-Chevalley health check on a canonical pullback square:
  let nat = @m1.mk_nat_ty()
  let c0 = @m1.Context::empty().extend_var("x", nat)
  let c1 = c0.extend_var("y", nat)
  let c2 = c0.extend_var("z", nat)
  let sq = @m5.build_context_pullback(1, c1, c2)
  let fib2 : @m5.FibredType = {
    base: c2,
    fiber_ty: @m1.mk_id_ty(nat, @m1.mk_var(1), @m1.mk_var(0)),
    smallness: @m2.AlgLevel::zero(),
  }
  let bc_ok = @m5.verify_beck_chevalley(sq, fib2)

  {
    arena_unique_nodes: self.arena.size(),
    context_depth: self.ctx.len(),
    universe_var_count: self.ugraph.num_vars,
    universe_longest_chain: strat.max_strict_chain.length(),
    universe_max_antichain: strat.max_antichain_width,
    certified_artifacts: self.artifacts.length(),
    galois_law_verified: galois_ok,
    beck_chevalley_verified: bc_ok,
  }
}
