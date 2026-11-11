///|
/// Module M13 — Categorical Fusion of M10 (Affine & Quantitative Type Theory),
/// M11 (Polymorphism, Implicit Unification/Rewriting, Coercions, Structural/Nominal),
/// M2 (Universe Constraint Graph), and M4 (Curry-Howard Proofs):
/// 1. Zero-Overhead Implicit Elaboration (`ElabTm -> QTerm` mapping `{x:A}` to `GZero`!)
/// 2. Universe-Polymorphic Scheme Constraint Allocation in M2 `UniverseGraph`
/// 3. O(1) Bitmask Structural Record Amalgamated Pushout (`mask1 | mask2`) & Restriction Coercions
/// 4. Substructural BCKW Proof Resource Stratifier (`Linear` vs `Affine` vs `Intuitionistic`)!

///|
pub(all) suberror QTTBridgeError {
  UnsolvedMetavariableInQTTBridge(Int32)
  UnsupportedElabConstructInQTT(String)
  ExpectedStructuralRecordTypes
  IncompatibleOverlappingField(Int32)
  UnsupportedCHProofInSubstructuralBridge
}

///|
/// 1. Theorem 13.1 (Zero-Overhead Quantitative Implicit Elaboration):
/// Compiles a solved M11 `ElabTm` into M10's `QTerm`:
/// - Every implicit binder/application (`is_implicit == true`) maps to `GZero` (0 runtime uses, erased by `erase_qtt_term`!)
/// - Every explicit binder/application (`is_implicit == false`) maps to `explicit_grade`!
pub fn compile_elab_to_qtt(
  tm : @m11.ElabTm,
  explicit_grade : @m10.Grade,
) -> @m10.QTerm raise QTTBridgeError {
  match tm {
    EVar(i) => QVar(i)
    EMeta(m, _) => raise QTTBridgeError::UnsolvedMetavariableInQTTBridge(m)
    EUniv(l) => QUniv(l)
    EBase("Unit") => QUnitTy
    EBase("Bool") => QBoolTy
    ESym("tt", _) => QUnitVal
    ESym("true", _) => QBoolVal(true)
    ESym("false", _) => QBoolVal(false)
    EPi(is_imp, x, a, b) => {
      let g : @m10.Grade = if is_imp { GZero } else { explicit_grade }
      QPi(
        g,
        x,
        compile_elab_to_qtt(a, explicit_grade),
        compile_elab_to_qtt(b, explicit_grade),
      )
    }
    ELam(is_imp, x, a, b) => {
      let g : @m10.Grade = if is_imp { GZero } else { explicit_grade }
      QLam(
        g,
        x,
        compile_elab_to_qtt(a, explicit_grade),
        compile_elab_to_qtt(b, explicit_grade),
      )
    }
    EApp(is_imp, f, a) => {
      let g : @m10.Grade = if is_imp { GZero } else { explicit_grade }
      QApp(
        g,
        compile_elab_to_qtt(f, explicit_grade),
        compile_elab_to_qtt(a, explicit_grade),
      )
    }
    EBase(s) | ESym(s, _) =>
      raise QTTBridgeError::UnsupportedElabConstructInQTT(s)
    EPatVar(_) | EPolyUniv(_) =>
      raise QTTBridgeError::UnsupportedElabConstructInQTT(
        "Uninstantiated Poly/Pat",
      )
  }
}

///|
/// 2. Allocate Fresh Universe Variables in M2's `UniverseGraph` for an M11 `DepPolyScheme`
/// with monotonic floor constraints `floors[i] <= u_i`, returning the allocated universe var IDs!
pub fn register_poly_scheme_universes(
  ugraph : @m2.UniverseGraph,
  scheme : @m11.DepPolyScheme,
  floors : Array[Int32],
) -> Array[Int32] raise Error {
  let vars : Array[Int32] = []
  for i = 0; i < scheme.univ_arity; i = i + 1 {
    let uv = ugraph.fresh_var()
    if i < floors.length() {
      ugraph.add_const_floor(floors[i], uv)
    }
    vars.push(uv)
  }
  let _ = ugraph.solve_minimal_valuation()
  vars
}

///|
/// 3. Amalgamated Pushout / Fibered Product of Structural Record Schemas (`組合範例.md` #3, #7):
/// Given `r1 = HStructRecord(m1, f1)` and `r2 = HStructRecord(m2, f2)` sharing field bits `m1 & m2`:
/// - Computes the meet/subtype on overlapping fields (`T_sub` that coerces to BOTH `f1[fid]` and `f2[fid]`!)
///   so the amalgamated record `apex` (`mask = m1 | m2`) comes equipped with TWO canonical synthesized
///   restriction coercions `proj1 : apex => r1` and `proj2 : apex => r2`!!
pub(all) struct StructuralRecordApex {
  shared_mask : UInt64
  union_mask : UInt64
  apex_record_ty : @m11.HybridTy
  coercion_to_left : @m11.CoercionProg
  coercion_to_right : @m11.CoercionProg
}

///|
pub fn amalgamate_structural_records(
  cenv : @m11.CoercionEnv,
  r1 : @m11.HybridTy,
  r2 : @m11.HybridTy,
) -> StructuralRecordApex raise Error {
  match (r1, r2) {
    (HStructRecord(m1, f1), HStructRecord(m2, f2)) => {
      let shared = m1 & m2
      let union_m = m1 | m2
      let entries : Array[(Int32, @m11.HybridTy)] = []
      for fid = 0; fid < 64; fid = fid + 1 {
        let in1 = ((m1 >> fid) & 1UL) != 0UL
        let in2 = ((m2 >> fid) & 1UL) != 0UL
        if in1 && in2 {
          let low = if fid == 0 { 0UL } else { (1UL << fid) - 1UL }
          let t1 = f1[@m11.popcount64(m1 & low)]
          let t2 = f2[@m11.popcount64(m2 & low)]
          // Pick common subtype `t_meet` that coerces to both `t1` and `t2`:
          if synthesize_coercion_exists(cenv, t1, t2) {
            entries.push((fid, t1))
          } else if synthesize_coercion_exists(cenv, t2, t1) {
            entries.push((fid, t2))
          } else {
            raise QTTBridgeError::IncompatibleOverlappingField(fid)
          }
        } else if in1 {
          let low = if fid == 0 { 0UL } else { (1UL << fid) - 1UL }
          entries.push((fid, f1[@m11.popcount64(m1 & low)]))
        } else if in2 {
          let low = if fid == 0 { 0UL } else { (1UL << fid) - 1UL }
          entries.push((fid, f2[@m11.popcount64(m2 & low)]))
        }
      }
      let apex_ty = @m11.mk_structural_record_ty(entries)
      let c1 = match @m11.synthesize_coercion(cenv, apex_ty, r1) {
        Some(p) => p
        None => raise QTTBridgeError::IncompatibleOverlappingField(-1)
      }
      let c2 = match @m11.synthesize_coercion(cenv, apex_ty, r2) {
        Some(p) => p
        None => raise QTTBridgeError::IncompatibleOverlappingField(-2)
      }
      {
        shared_mask: shared,
        union_mask: union_m,
        apex_record_ty: apex_ty,
        coercion_to_left: c1,
        coercion_to_right: c2,
      }
    }
    _ => raise QTTBridgeError::ExpectedStructuralRecordTypes
  }
}

///|
fn synthesize_coercion_exists(
  cenv : @m11.CoercionEnv,
  a : @m11.HybridTy,
  b : @m11.HybridTy,
) -> Bool {
  match @m11.synthesize_coercion(cenv, a, b) {
    Some(_) => true
    None => false
  }
}

///|
/// 4. Substructural BCKW Curry-Howard Proof Classifier (`classify_substructural_proof`):
/// Translates M4 propositional proofs (`TUnit`, `TProd`, `TArrow`) into M10 `QTerm` under candidate
/// grades `[GOne (Linear BCI), GAffine (Affine BCK), GOmega (Full Intuitionistic BCKW)]`
/// and determines the sharpest substructural logic fragment inhabited by the proof!
#derive(Eq, Debug)
pub(all) enum SubstructuralClass {
  StrictLinearBCI
  AffineBCK
  UnrestrictedIntuitionistic
}

///|
pub extend SubstructuralClass with Eq::{equal, not_equal}

///|
pub extend SubstructuralClass with @debug.Debug::{to_repr}

///|
fn ch_type_to_qtype(
  ty : @m4.CHType,
  g : @m10.Grade,
) -> @m10.QTerm raise QTTBridgeError {
  match ty {
    TUnit => QUnitTy
    TPredFamily("Bool", _) => QBoolTy
    TArrow(a, b) => {
      let qa = ch_type_to_qtype(a, g)
      let qb = @m10.shift_qterm(ch_type_to_qtype(b, g), 1, 0)
      QPi(g, "_", qa, qb)
    }
    TProd(a, b) => {
      let qa = ch_type_to_qtype(a, g)
      let qb = @m10.shift_qterm(ch_type_to_qtype(b, g), 1, 0)
      QSigma(g, "_", qa, qb)
    }
    _ => raise QTTBridgeError::UnsupportedCHProofInSubstructuralBridge
  }
}

///|
fn ch_proof_to_qterm(
  prf : @m4.CHTerm,
  ctx_tys : Array[@m4.CHType],
  g : @m10.Grade,
) -> @m10.QTerm raise Error {
  match prf {
    PTVar(i) => QVar(i)
    PTUnit => QUnitVal
    PTLam(dom, body) => {
      let qdom = ch_type_to_qtype(dom, g)
      let next_ctx = ctx_tys.copy()
      next_ctx.push(dom)
      QLam(g, "h", qdom, ch_proof_to_qterm(body, next_ctx, g))
    }
    PTApp(f, a) =>
      QApp(
        g,
        ch_proof_to_qterm(f, ctx_tys, g),
        ch_proof_to_qterm(a, ctx_tys, g),
      )
    PTPair(a, b) => {
      let ta = @m4.infer_ch_term(ctx_tys, a)
      let tb = @m4.infer_ch_term(ctx_tys, b)
      let sig_ty = ch_type_to_qtype(TProd(ta, tb), g)
      QTensorPair(
        g,
        ch_proof_to_qterm(a, ctx_tys, g),
        ch_proof_to_qterm(b, ctx_tys, g),
        sig_ty,
      )
    }
    _ => raise QTTBridgeError::UnsupportedCHProofInSubstructuralBridge
  }
}

///|
pub fn classify_substructural_proof(
  prf : @m4.CHTerm,
) -> SubstructuralClass raise Error {
  let _ = @m4.infer_ch_term([], prf)
  let q_lin = ch_proof_to_qterm(prf, [], GOne)
  let is_lin = try {
    let _ = @m10.verify_qtt_judgment([], q_lin)
    true
  } catch {
    _ => false
  }
  if is_lin {
    return StrictLinearBCI
  }
  let q_aff = ch_proof_to_qterm(prf, [], GAffine)
  let is_aff = try {
    let _ = @m10.verify_qtt_judgment([], q_aff)
    true
  } catch {
    _ => false
  }
  if is_aff {
    return AffineBCK
  }
  let q_om = ch_proof_to_qterm(prf, [], GOmega)
  let _ = @m10.verify_qtt_judgment([], q_om)
  UnrestrictedIntuitionistic
}
