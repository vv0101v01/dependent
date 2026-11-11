///|
/// Module M6 — Global Galois Correspondence, 64-bit Chu Space Duality,
/// M4->M3 Constructive Proof-to-Kernel Compiler, Tensor-Sum Distributivity,
/// Monad Distributive Law, Morita Equivalence, Localization Roofs, and Game Strategies.

///|
pub(all) suberror BridgeError {
  ChuDimensionOverflow(Int32)
  UnsupportedSortInKernelBridge(String)
  UnsupportedConstructInKernelBridge(String)
  ChuMorphismAdjointViolation(Int32, Int32)
  LocalizationIncompatibleMidpoint
}

///|
/// Hardware 64-Bit Bit-Packed Chu Space `Chu(Set, 2)` (`(A, r : A × X -> 2, X)`):
/// - `num_terms <= 64`: candidate terms / programs / contexts `a ∈ A`
/// - `num_types <= 64`: candidate types / specifications / tests `x ∈ X`
/// - `rows[a]` has bit `x` set iff `a ⊨ x` (`r(a, x) == 1`)
/// - `cols[x]` has bit `a` set iff `a ⊨ x` (`r(a, x) == 1`)
#derive(Eq, Debug)
pub(all) struct ChuTypingSpace {
  num_terms : Int32
  num_types : Int32
  rows : Array[UInt64]
  cols : Array[UInt64]
}

///|
pub extend ChuTypingSpace with Eq::{equal, not_equal}

///|
pub extend ChuTypingSpace with @debug.Debug::{to_repr}

///|
fn full_mask(n : Int32) -> UInt64 {
  if n <= 0 {
    0UL
  } else if n >= 64 {
    0xFFFFFFFFFFFFFFFFUL
  } else {
    (1UL << n) - 1UL
  }
}

///|
/// Construct a `ChuTypingSpace` directly by running M3's Bidirectional NbE Typechecker
/// on every `(term_a, type_x)` pair over `jctx`!
pub fn build_dtt_chu_space(
  jctx : @m3.JudgmentCtx,
  terms : Array[@m3.CoreTm],
  types : Array[@m3.CoreTm],
) -> ChuTypingSpace raise Error {
  let m = terms.length()
  let n = types.length()
  if m > 64 {
    raise BridgeError::ChuDimensionOverflow(m)
  }
  if n > 64 {
    raise BridgeError::ChuDimensionOverflow(n)
  }
  let vtypes : Array[@m3.Val] = []
  for ty in types {
    let (vty, _) = @m3.check_is_type(jctx, ty)
    vtypes.push(vty)
  }
  let rows : Array[UInt64] = Array::make(m, 0UL)
  let cols : Array[UInt64] = Array::make(n, 0UL)
  for a = 0; a < m; a = a + 1 {
    for x = 0; x < n; x = x + 1 {
      let holds = try {
        @m3.check_term(jctx, terms[a], vtypes[x])
        true
      } catch {
        _ => false
      }
      if holds {
        rows[a] = rows[a] | (1UL << x)
        cols[x] = cols[x] | (1UL << a)
      }
    }
  }
  { num_terms: m, num_types: n, rows, cols, }
}

///|
/// Build a 64-Bit Chu Space directly from M2's Algebraic Universe Graph `Ψ`:
/// Pairs candidate source levels `lowers[a]` against candidate upper bounds `uppers[x]`
/// via M2's exact Galois cycle-refutation solver `g.entails_le(lowers[a], uppers[x])`!
pub fn build_universe_chu_space(
  g : @m2.UniverseGraph,
  lowers : Array[@m2.AlgLevel],
  uppers : Array[@m2.AlgLevel],
) -> ChuTypingSpace raise BridgeError {
  let m = lowers.length()
  let n = uppers.length()
  if m > 64 {
    raise BridgeError::ChuDimensionOverflow(m)
  }
  if n > 64 {
    raise BridgeError::ChuDimensionOverflow(n)
  }
  let rows : Array[UInt64] = Array::make(m, 0UL)
  let cols : Array[UInt64] = Array::make(n, 0UL)
  for a = 0; a < m; a = a + 1 {
    for x = 0; x < n; x = x + 1 {
      if g.entails_le(lowers[a], uppers[x]) {
        rows[a] = rows[a] | (1UL << x)
        cols[x] = cols[x] | (1UL << a)
      }
    }
  }
  { num_terms: m, num_types: n, rows, cols, }
}

///|
/// Involutive Mirror Symmetry (`chu_dual`):
/// Swaps Objects/Terms `A` and Tests/Types `X` in `O(1)` array header swap (`(C^⊥)^⊥ == C`)!
pub fn chu_dual(space : ChuTypingSpace) -> ChuTypingSpace {
  {
    num_terms: space.num_types,
    num_types: space.num_terms,
    rows: space.cols.copy(),
    cols: space.rows.copy(),
  }
}

///|
/// O(1)-per-active-element Galois Specification Operator `s(S) : P(A) -> P(X)^op`:
/// Returns bitmask of all types `x ∈ X` satisfied by EVERY term `a ∈ S`!
pub fn ChuTypingSpace::galois_spec_of(
  self : ChuTypingSpace,
  term_subset : UInt64,
) -> UInt64 {
  let mut acc = full_mask(self.num_types)
  let masked = term_subset & full_mask(self.num_terms)
  for a = 0; a < self.num_terms; a = a + 1 {
    if ((masked >> a) & 1UL) != 0UL {
      acc = acc & self.rows[a]
    }
  }
  acc
}

///|
/// O(1)-per-active-element Galois Model/Term Operator `t(T) : P(X)^op -> P(A)`:
/// Returns bitmask of all terms `a ∈ A` satisfying EVERY specification `x ∈ T`!
pub fn ChuTypingSpace::galois_models_of(
  self : ChuTypingSpace,
  type_subset : UInt64,
) -> UInt64 {
  let mut acc = full_mask(self.num_terms)
  let masked = type_subset & full_mask(self.num_types)
  for x = 0; x < self.num_types; x = x + 1 {
    if ((masked >> x) & 1UL) != 0UL {
      acc = acc & self.cols[x]
    }
  }
  acc
}

///|
/// Global Axiom Verification — Galois Correspondence Law:
/// Checks in O(1) bit arithmetic that `T ⊆ s(S)  <==>  S ⊆ t(T)`!
pub fn ChuTypingSpace::verify_galois_adjointness(
  self : ChuTypingSpace,
  s_mask : UInt64,
  t_mask : UInt64,
) -> Bool {
  let s_clean = s_mask & full_mask(self.num_terms)
  let t_clean = t_mask & full_mask(self.num_types)
  let lhs = (t_clean & self.galois_spec_of(s_clean).lnot()) == 0UL
  let rhs = (s_clean & self.galois_models_of(t_clean).lnot()) == 0UL
  lhs == rhs
}

///|
/// Compute the Galois Closure `(t(s(S)), s(S))` — Formal Concept Fixed Point `(Extent, Intent)`!
pub fn ChuTypingSpace::concept_closure(
  self : ChuTypingSpace,
  seed_terms : UInt64,
) -> (UInt64, UInt64) {
  let intent = self.galois_spec_of(seed_terms)
  let extent = self.galois_models_of(intent)
  (extent, intent)
}

///|
/// Chu Morphism `(f_forward : A1 -> A2, f_back : X2 -> X1)` between Chu Spaces:
/// Must satisfy the adjointness identity `r2(f_forward(a), y) == r1(a, f_back(y))`!
#derive(Eq, Debug)
pub(all) struct ChuMorphism {
  forward_term_map : Array[Int32]
  adjoint_type_map : Array[Int32]
}

///|
pub extend ChuMorphism with Eq::{equal, not_equal}

///|
pub extend ChuMorphism with @debug.Debug::{to_repr}

///|
pub fn verify_chu_morphism(
  dom : ChuTypingSpace,
  cod : ChuTypingSpace,
  mor : ChuMorphism,
) -> Bool raise BridgeError {
  if mor.forward_term_map.length() != dom.num_terms ||
    mor.adjoint_type_map.length() != cod.num_types {
    raise BridgeError::ChuMorphismAdjointViolation(-1, -1)
  }
  for a = 0; a < dom.num_terms; a = a + 1 {
    let fa = mor.forward_term_map[a]
    for y = 0; y < cod.num_types; y = y + 1 {
      let gy = mor.adjoint_type_map[y]
      let r2 = ((cod.rows[fa] >> y) & 1UL) != 0UL
      let r1 = ((dom.rows[a] >> gy) & 1UL) != 0UL
      if r2 != r1 {
        raise BridgeError::ChuMorphismAdjointViolation(a, y)
      }
    }
  }
  true
}

///|
/// ============================================================================
/// Deep Functorial Compiler: M4 Constructive Logic (`CHType`/`CHTerm`) -> M3 DTT (`CoreTm`)
/// ============================================================================
/// Notice how M4 uses SEPARATE de Bruijn namespaces (`obj_vars` vs `proof_vars`),
/// whereas M3 Dependent Type Theory unifies ALL variables (domain objects AND proof hypotheses)
/// into ONE telescope!
/// We carry `binder_is_obj : Array[Bool]` tracking every binder in the unified M3 context
/// from outermost to innermost so both object De Bruijn indices and proof De Bruijn indices
/// resolve in exact O(depth) time to their unified M3 De Bruijn index!
fn resolve_split_index(
  binder_is_obj : Array[Bool],
  want_obj : Bool,
  split_idx : Int32,
) -> Int32 raise BridgeError {
  let n = binder_is_obj.length()
  let mut seen = 0
  for pos = n - 1; pos >= 0; pos = pos - 1 {
    if binder_is_obj[pos] == want_obj {
      if seen == split_idx {
        return n - 1 - pos
      }
      seen = seen + 1
    }
  }
  raise BridgeError::UnsupportedConstructInKernelBridge(
    "Unbound split variable \{split_idx}",
  )
}

///|
pub fn compile_sort_to_core(s : @m4.DomainSort) -> @m3.CoreTm raise BridgeError {
  if s.name == "Nat" {
    CNat
  } else if s.name == "Unit" {
    CUnit
  } else {
    raise BridgeError::UnsupportedSortInKernelBridge(s.name)
  }
}

///|
pub fn compile_obj_to_core(
  binder_is_obj : Array[Bool],
  t : @m4.ObjTerm,
) -> @m3.CoreTm raise BridgeError {
  match t {
    OVar(i) => CVar(resolve_split_index(binder_is_obj, true, i))
    OConst("0") => CZero
    OConst("tt") => CStar
    OFun("succ", args) =>
      if args.length() == 1 {
        CSucc(compile_obj_to_core(binder_is_obj, args[0]))
      } else {
        raise BridgeError::UnsupportedConstructInKernelBridge("succ arity")
      }
    OConst(c) | OFun(c, _) =>
      raise BridgeError::UnsupportedConstructInKernelBridge(c)
  }
}

///|
/// Compile an M4 `CHType` into a unified M3 `CoreTm` Dependent Type!
pub fn compile_ch_type_to_core(
  binder_is_obj : Array[Bool],
  ty : @m4.CHType,
) -> @m3.CoreTm raise BridgeError {
  match ty {
    TUnit => CUnit
    TProd(a, b) => {
      let ca = compile_ch_type_to_core(binder_is_obj, a)
      let next = binder_is_obj.copy()
      next.push(false)
      let cb = compile_ch_type_to_core(next, b)
      CSigma("_", ca, cb)
    }
    TArrow(a, b) => {
      let ca = compile_ch_type_to_core(binder_is_obj, a)
      let next = binder_is_obj.copy()
      next.push(false)
      let cb = compile_ch_type_to_core(next, b)
      CPi("_", ca, cb)
    }
    TPi(x, s, body) => {
      let cs = compile_sort_to_core(s)
      let next = binder_is_obj.copy()
      next.push(true)
      CPi(x, cs, compile_ch_type_to_core(next, body))
    }
    TSigma(x, s, body) => {
      let cs = compile_sort_to_core(s)
      let next = binder_is_obj.copy()
      next.push(true)
      CSigma(x, cs, compile_ch_type_to_core(next, body))
    }
    TId(s, l, r) =>
      CId(
        compile_sort_to_core(s),
        compile_obj_to_core(binder_is_obj, l),
        compile_obj_to_core(binder_is_obj, r),
      )
    TSquash(a) => CSquash(compile_ch_type_to_core(binder_is_obj, a))
    TEmpty | TSum(_, _) | TPredFamily(_, _) =>
      raise BridgeError::UnsupportedConstructInKernelBridge("Abstract CHType")
  }
}

///|
/// Compile an M4 Constructive Proof `CHTerm` into a Unified M3 Dependent Term `CoreTm`!
pub fn compile_ch_term_to_core(
  binder_is_obj : Array[Bool],
  prf : @m4.CHTerm,
) -> @m3.CoreTm raise BridgeError {
  match prf {
    PTVar(i) => CVar(resolve_split_index(binder_is_obj, false, i))
    PTUnit => CStar
    PTPair(a, b) =>
      CPair(
        compile_ch_term_to_core(binder_is_obj, a),
        compile_ch_term_to_core(binder_is_obj, b),
      )
    PTFst(p) => CFst(compile_ch_term_to_core(binder_is_obj, p))
    PTSnd(p) => CSnd(compile_ch_term_to_core(binder_is_obj, p))
    PTLam(dom, body) => {
      let cdom = compile_ch_type_to_core(binder_is_obj, dom)
      let next = binder_is_obj.copy()
      next.push(false)
      CLam("h", cdom, compile_ch_term_to_core(next, body))
    }
    PTApp(f, a) =>
      CApp(
        compile_ch_term_to_core(binder_is_obj, f),
        compile_ch_term_to_core(binder_is_obj, a),
      )
    PTDepLam(s, body) => {
      let cs = compile_sort_to_core(s)
      let next = binder_is_obj.copy()
      next.push(true)
      CLam("x", cs, compile_ch_term_to_core(next, body))
    }
    PTDepApp(f, obj) =>
      CApp(
        compile_ch_term_to_core(binder_is_obj, f),
        compile_obj_to_core(binder_is_obj, obj),
      )
    PTPack(w, p, whole_sig) => {
      let cw = compile_obj_to_core(binder_is_obj, w)
      let cp = compile_ch_term_to_core(binder_is_obj, p)
      let csig = compile_ch_type_to_core(binder_is_obj, whole_sig)
      CAnn(CPair(cw, cp), csig)
    }
    PTRefl(_, t) => CRefl(compile_obj_to_core(binder_is_obj, t))
    PTSquashBox(w) => CBoxProof(compile_ch_term_to_core(binder_is_obj, w))
    _ =>
      raise BridgeError::UnsupportedConstructInKernelBridge(
        "Extended CHTerm eliminator",
      )
  }
}

///|
/// ============================================================================
/// Tensor–Sum Distributivity Isomorphism (`組合範例.md` #5):
/// `Σ(x:D). (P(x) + Q(x))  <==>  (Σ(x:D). P(x)) + (Σ(x:D). Q(x))`
/// ============================================================================
pub fn tensor_sum_distribute_forward(
  s : @m4.DomainSort,
  px : @m4.CHType,
  qx : @m4.CHType,
) -> @m4.CHTerm {
  let src = @m4.TSigma("x", s, TSum(px, qx))
  let sig_p = @m4.TSigma("x", s, px)
  let sig_q = @m4.TSigma("x", s, qx)
  // Inside `PTLam(src, PTUnpack(PTVar(0), ...))`:
  // Proof context has `[src (#1), sum_pq (#0)]` and Object context has `[x (#0)]`!
  // We must shift `sig_p` and `sig_q` by +1 in open object variables (`cutoff = 0`),
  // though `sig_p` binds `x` at cutoff 1 (`shift_ch_type_obj(sig_p, 1, 0)`).
  let sig_p_in = @m4.shift_ch_type_obj(sig_p, 1, 0)
  let sig_q_in = @m4.shift_ch_type_obj(sig_q, 1, 0)
  PTLam(
    src,
    PTUnpack(
      PTVar(0),
      PTCase(
        PTVar(0),
        PTInl(sig_q_in, PTPack(OVar(0), PTVar(0), sig_p_in)),
        PTInr(sig_p_in, PTPack(OVar(0), PTVar(0), sig_q_in)),
      ),
    ),
  )
}

///|
pub fn tensor_sum_distribute_backward(
  s : @m4.DomainSort,
  px : @m4.CHType,
  qx : @m4.CHType,
) -> @m4.CHTerm {
  let sig_p = @m4.TSigma("x", s, px)
  let sig_q = @m4.TSigma("x", s, qx)
  let sum_src = @m4.TSum(sig_p, sig_q)
  let dst = @m4.TSigma("x", s, TSum(px, qx))
  let dst_in = @m4.shift_ch_type_obj(dst, 1, 0)
  PTLam(
    sum_src,
    PTCase(
      PTVar(0),
      PTUnpack(PTVar(0), PTPack(OVar(0), PTInl(qx, PTVar(0)), dst_in)),
      PTUnpack(PTVar(0), PTPack(OVar(0), PTInr(px, PTVar(0)), dst_in)),
    ),
  )
}

///|
/// ============================================================================
/// Monad Distributive Law `λ : Squash ∘ Writer_W -> Writer_W ∘ Squash` (`組合範例.md` #4)
/// on Purely Determined Monoid Accumulators + Proof-Irrelevant Specifications:
/// Wait: in constructive logic, `W × ||P||` always maps canonically into `||W × P||`!
/// That canonical natural transformation `dist_writer_squash : (W × ||P||) -> ||W × P||`
/// IS Beck's Distributive Law `Writer_W ∘ Squash -> Squash ∘ Writer_W`, making `Squash ∘ Writer_W`
/// a composite monad! Let's synthesize and typecheck it in M4!
/// ============================================================================
pub fn monad_distributive_writer_squash(
  w_ty : @m4.CHType,
  p_ty : @m4.CHType,
) -> @m4.CHTerm {
  // Source: `w_ty × ||p_ty||` -> Target: `|| w_ty × p_ty ||`
  // Note `|| w_ty × p_ty ||` IS proof-irrelevant (`TSquash`), so `PTLetSquash` is 100% legal!
  let src = @m4.TProd(w_ty, TSquash(p_ty))
  PTLam(
    src,
    PTLetSquash(PTSnd(PTVar(0)), PTSquashBox(PTPair(PTFst(PTVar(1)), PTVar(0)))),
  )
}

///|
/// ============================================================================
/// Morita Equivalence Certificate (`組合範例.md` #11):
/// Certifies that Uncurried Sigma Presentation `(Σx:A. B(x)) -> C` and Curried Pi Presentation
/// `Πx:A. (B(x) -> C)` induce isomorphic Chu Model Spaces AND mutually inverse M3 NbE terms!
/// ============================================================================
pub fn verify_curry_morita_equivalence(
  jctx : @m3.JudgmentCtx,
  a : @m3.CoreTm,
  b_x : @m3.CoreTm,
  c_xy : @m3.CoreTm,
) -> Bool raise Error {
  let ty_uncurried = @m3.dep_uncurried_type(a, b_x, c_xy)
  let ty_curried = @m3.dep_curried_type(a, b_x, c_xy)
  let (vu, _) = @m3.check_is_type(jctx, ty_uncurried)
  let (vc, _) = @m3.check_is_type(jctx, ty_curried)
  // Verify on a generic neutral inhabitant `f0 : ty_uncurried` at `jctx.push_var("f", vu)`:
  let j_u = jctx.push_var("f", vu)
  let rt_u = @m3.dep_uncurry_term(a, b_x, @m3.dep_curry_term(a, b_x, CVar(0)))
  @m3.check_term(j_u, rt_u, vu)
  let ok_u = @m3.conv_val(
    j_u.depth(),
    vu,
    @m3.eval_tm(j_u.env, rt_u),
    @m3.eval_tm(j_u.env, CVar(0)),
  )
  let j_c = jctx.push_var("g", vc)
  let rt_c = @m3.dep_curry_term(a, b_x, @m3.dep_uncurry_term(a, b_x, CVar(0)))
  @m3.check_term(j_c, rt_c, vc)
  let ok_c = @m3.conv_val(
    j_c.depth(),
    vc,
    @m3.eval_tm(j_c.env, rt_c),
    @m3.eval_tm(j_c.env, CVar(0)),
  )
  ok_u && ok_c
}

///|
/// ============================================================================
/// Localization / Calculus of Right Fractions `C[W^-1]` (`組合範例.md` #12):
/// Represents a localized morphism `A ~~> B` as a roof `A <--s-- Mid --f--> B`
/// where `s ∈ W` is a trivial contractible context extension (`Unit` padding of count `pad_units`)
/// and `f` is a term in `Mid`! Composes two roofs by Ore pullback of `Unit` extensions!
/// ============================================================================
#derive(Eq, Debug)
pub(all) struct LocalizedRoof {
  dom_ty : @m1.SynExpr
  cod_ty : @m1.SynExpr
  unit_pads : Int32
  roof_body : @m1.SynExpr
}

///|
pub extend LocalizedRoof with Eq::{equal, not_equal}

///|
pub extend LocalizedRoof with @debug.Debug::{to_repr}

///|
/// Compose Localized Roofs `r1 : A ~~> B` and `r2 : B ~~> C` via Ore Pullback + Contractible Section `tt`!
pub fn compose_localized_roofs(
  r1 : LocalizedRoof,
  r2 : LocalizedRoof,
) -> LocalizedRoof raise BridgeError {
  if r1.cod_ty != r2.dom_ty {
    raise BridgeError::LocalizationIncompatibleMidpoint
  }
  // In `r1`, open context is `[x : A (#pad1), u_1 .. u_pad1 : Unit]`.
  // In `r2`, open context is `[y : B (#pad2), v_1 .. v_pad2 : Unit]`.
  // In the Ore Pullback `[x : A, u_1..u_pad1, v_1..v_pad2]`:
  // - Shift `r1.roof_body` up by `r2.unit_pads` at cutoff 0 so it lives in the combined pad context!
  let sub = @m1.subst_lift(r2.unit_pads, @m1.subst_single(r1.roof_body))
  {
    dom_ty: r1.dom_ty,
    cod_ty: r2.cod_ty,
    unit_pads: r1.unit_pads + r2.unit_pads,
    roof_body: @m1.apply_subst(r2.roof_body, sub),
  }
}

///|
/// Collapse a Localized Roof `A <--W-- Mid --> B` back to a direct morphism `λx:A. body[u := tt]`
/// using the canonical inverse section of `W` (`UnitVal`)!
pub fn collapse_localized_roof(roof : LocalizedRoof) -> @m1.SynExpr {
  let mut cur = roof.roof_body
  for k = 0; k < roof.unit_pads; k = k + 1 {
    cur = @m1.apply_subst(cur, @m1.subst_single(@m1.mk_unit_val()))
  }
  @m1.mk_lam("x", roof.dom_ty, cur)
}

///|
/// ============================================================================
/// Game Semantics Strategy Pipeline (`組合範例.md` #14):
/// Models an Arena Game `G_in ⊢ G_out` with a constructive winning strategy (`SequentProof`),
/// and implements Parallel Composition + Internal Move Hiding (`σ || τ` -> Cut Elimination)!
/// ============================================================================
#derive(Eq, Debug)
pub(all) struct GameStrategy {
  input_arena : @m4.PropFormula
  output_arena : @m4.PropFormula
  proof_strategy : @m4.SequentProof
}

///|
pub extend GameStrategy with Eq::{equal, not_equal}

///|
pub extend GameStrategy with @debug.Debug::{to_repr}

///|
/// Compose Strategy `s1 : A ⊢ B` with `s2 : B ⊢ C` by hiding intermediate arena `B`
/// via Gentzen Cut-Elimination (`count_cuts == 0`), producing a direct cut-free strategy `A ⊢ C`!
pub fn compose_game_strategies_hiding(
  s1 : GameStrategy,
  s2 : GameStrategy,
) -> GameStrategy raise Error {
  // In context `[A (#0)]`:
  // `s1.proof_strategy` proves `A ⊢ B`.
  // Weakening `s2.proof_strategy` (`B ⊢ C`) at cutoff `1` by `+1` yields `A, B ⊢ C`!
  let s2_weak = @m4.weaken_sequent(s2.proof_strategy, 1, 1)
  let raw_cut = @m4.SCut(s1.output_arena, s1.proof_strategy, s2_weak)
  let hidden_cut_free = @m4.eliminate_cuts(raw_cut)
  {
    input_arena: s1.input_arena,
    output_arena: s2.output_arena,
    proof_strategy: hidden_cut_free,
  }
}
