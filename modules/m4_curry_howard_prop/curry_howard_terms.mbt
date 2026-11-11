///|
/// Module M4 — Curry-Howard Correspondence & Propositions-as-Types:
/// First-Order Constructive Dependent Predicate Logic <-> Dependent Proof Calculus,
/// Squash Proof-Irrelevance Reflection, and BHK Proof Normalization.

///|
pub suberror LogicError {
  UnboundProofVar(Int32)
  ProofTypeMismatch(CHType, CHType)
  ExpectedFunctionProof(CHType)
  ExpectedProductProof(CHType)
  ExpectedSumProof(CHType)
  ExpectedForallProof(CHType)
  ExpectedExistsProof(CHType)
  SquashEliminationIntoRelevantType(CHType)
  InvalidSequentRule(String)
}

///|
#derive(Eq, Debug)
pub(all) struct DomainSort {
  name : String
}

///|
pub extend DomainSort with Eq::{equal, not_equal}

///|
pub extend DomainSort with @debug.Debug::{to_repr}

///|
#derive(Eq, Debug)
pub(all) enum ObjTerm {
  OVar(Int32)
  OConst(String)
  OFun(String, Array[ObjTerm])
}

///|
pub extend ObjTerm with Eq::{equal, not_equal}

///|
pub extend ObjTerm with @debug.Debug::{to_repr}

///|
pub fn shift_obj_term(t : ObjTerm, delta : Int32, cutoff : Int32) -> ObjTerm {
  if delta == 0 {
    return t
  }
  match t {
    OVar(i) => if i >= cutoff { OVar(i + delta) } else { t }
    OConst(_) => t
    OFun(f, args) => {
      let next : Array[ObjTerm] = []
      for a in args {
        next.push(shift_obj_term(a, delta, cutoff))
      }
      OFun(f, next)
    }
  }
}

///|
pub fn subst_obj_term(t : ObjTerm, target : Int32, repl : ObjTerm) -> ObjTerm {
  match t {
    OVar(i) =>
      if i == target {
        shift_obj_term(repl, target, 0)
      } else if i > target {
        OVar(i - 1)
      } else {
        t
      }
    OConst(_) => t
    OFun(f, args) => {
      let next : Array[ObjTerm] = []
      for a in args {
        next.push(subst_obj_term(a, target, repl))
      }
      OFun(f, next)
    }
  }
}

///|
/// First-Order Dependent Constructive Predicate Formulas (with Squash Modality)
#derive(Eq, Debug)
pub(all) enum PropFormula {
  FTop
  FBot
  FAtom(String, Array[ObjTerm])
  FEq(DomainSort, ObjTerm, ObjTerm)
  FConj(PropFormula, PropFormula)
  FDisj(PropFormula, PropFormula)
  FImpl(PropFormula, PropFormula)
  FForall(String, DomainSort, PropFormula)
  FExists(String, DomainSort, PropFormula)
  FSquash(PropFormula)
}

///|
pub extend PropFormula with Eq::{equal, not_equal}

///|
pub extend PropFormula with @debug.Debug::{to_repr}

///|
/// Curry-Howard Target Dependent Types
#derive(Eq, Debug)
pub(all) enum CHType {
  TUnit
  TEmpty
  TPredFamily(String, Array[ObjTerm])
  TId(DomainSort, ObjTerm, ObjTerm)
  TProd(CHType, CHType)
  TSum(CHType, CHType)
  TArrow(CHType, CHType)
  TPi(String, DomainSort, CHType)
  TSigma(String, DomainSort, CHType)
  TSquash(CHType)
}

///|
pub extend CHType with Eq::{equal, not_equal}

///|
pub extend CHType with @debug.Debug::{to_repr}

///|
/// Global Axiom (Curry-Howard Forward Isomorphism `⟦-⟧ : Formula -> Type`).
pub fn formula_to_ch_type(f : PropFormula) -> CHType {
  match f {
    FTop => TUnit
    FBot => TEmpty
    FAtom(p, args) => TPredFamily(p, args.copy())
    FEq(s, l, r) => TId(s, l, r)
    FConj(a, b) => TProd(formula_to_ch_type(a), formula_to_ch_type(b))
    FDisj(a, b) => TSum(formula_to_ch_type(a), formula_to_ch_type(b))
    FImpl(a, b) => TArrow(formula_to_ch_type(a), formula_to_ch_type(b))
    FForall(x, d, body) => TPi(x, d, formula_to_ch_type(body))
    FExists(x, d, body) => TSigma(x, d, formula_to_ch_type(body))
    FSquash(a) => TSquash(formula_to_ch_type(a))
  }
}

///|
/// Global Axiom (Curry-Howard Inverse Isomorphism `⟦-⟧^-1 : Type -> Formula`).
pub fn ch_type_to_formula(ty : CHType) -> PropFormula {
  match ty {
    TUnit => FTop
    TEmpty => FBot
    TPredFamily(p, args) => FAtom(p, args.copy())
    TId(s, l, r) => FEq(s, l, r)
    TProd(a, b) => FConj(ch_type_to_formula(a), ch_type_to_formula(b))
    TSum(a, b) => FDisj(ch_type_to_formula(a), ch_type_to_formula(b))
    TArrow(a, b) => FImpl(ch_type_to_formula(a), ch_type_to_formula(b))
    TPi(x, d, body) => FForall(x, d, ch_type_to_formula(body))
    TSigma(x, d, body) => FExists(x, d, ch_type_to_formula(body))
    TSquash(a) => FSquash(ch_type_to_formula(a))
  }
}

///|
/// Shift object-variable De Bruijn indices inside `CHType`.
pub fn shift_ch_type_obj(ty : CHType, delta : Int32, cutoff : Int32) -> CHType {
  if delta == 0 {
    return ty
  }
  match ty {
    TUnit | TEmpty => ty
    TPredFamily(p, args) => {
      let next : Array[ObjTerm] = []
      for a in args {
        next.push(shift_obj_term(a, delta, cutoff))
      }
      TPredFamily(p, next)
    }
    TId(s, l, r) =>
      TId(s, shift_obj_term(l, delta, cutoff), shift_obj_term(r, delta, cutoff))
    TProd(a, b) =>
      TProd(
        shift_ch_type_obj(a, delta, cutoff),
        shift_ch_type_obj(b, delta, cutoff),
      )
    TSum(a, b) =>
      TSum(
        shift_ch_type_obj(a, delta, cutoff),
        shift_ch_type_obj(b, delta, cutoff),
      )
    TArrow(a, b) =>
      TArrow(
        shift_ch_type_obj(a, delta, cutoff),
        shift_ch_type_obj(b, delta, cutoff),
      )
    TPi(x, d, body) => TPi(x, d, shift_ch_type_obj(body, delta, cutoff + 1))
    TSigma(x, d, body) =>
      TSigma(x, d, shift_ch_type_obj(body, delta, cutoff + 1))
    TSquash(a) => TSquash(shift_ch_type_obj(a, delta, cutoff))
  }
}

///|
/// Substitute object variable `target` with `repl` in `CHType`.
pub fn subst_ch_type_obj(ty : CHType, target : Int32, repl : ObjTerm) -> CHType {
  match ty {
    TUnit | TEmpty => ty
    TPredFamily(p, args) => {
      let next : Array[ObjTerm] = []
      for a in args {
        next.push(subst_obj_term(a, target, repl))
      }
      TPredFamily(p, next)
    }
    TId(s, l, r) =>
      TId(s, subst_obj_term(l, target, repl), subst_obj_term(r, target, repl))
    TProd(a, b) =>
      TProd(
        subst_ch_type_obj(a, target, repl),
        subst_ch_type_obj(b, target, repl),
      )
    TSum(a, b) =>
      TSum(
        subst_ch_type_obj(a, target, repl),
        subst_ch_type_obj(b, target, repl),
      )
    TArrow(a, b) =>
      TArrow(
        subst_ch_type_obj(a, target, repl),
        subst_ch_type_obj(b, target, repl),
      )
    TPi(x, d, body) => TPi(x, d, subst_ch_type_obj(body, target + 1, repl))
    TSigma(x, d, body) =>
      TSigma(x, d, subst_ch_type_obj(body, target + 1, repl))
    TSquash(a) => TSquash(subst_ch_type_obj(a, target, repl))
  }
}

///|
/// Subsingleton / Strict Proof-Irrelevance Predicate (`is_prop_irrelevant`):
/// Closed under `TUnit`, `TEmpty`, `TSquash(_)`, `TProd` of irrelevant types,
/// `TArrow(_, irr)` and `TPi(_, _, irr)` (Heyting Sublocale / Modal Reflector Closure!).
pub fn is_prop_irrelevant(ty : CHType) -> Bool {
  match ty {
    TUnit | TEmpty | TSquash(_) | TId(_, _, _) => true
    TProd(a, b) => is_prop_irrelevant(a) && is_prop_irrelevant(b)
    TArrow(_, b) => is_prop_irrelevant(b)
    TPi(_, _, b) => is_prop_irrelevant(b)
    TPredFamily(_, _) | TSum(_, _) | TSigma(_, _, _) => false
  }
}

///|
/// BHK Constructive Proof Terms (Natural Deduction Curry-Howard Programs)
#derive(Eq, Debug)
pub(all) enum CHTerm {
  PTVar(Int32)
  PTUnit
  PTAbsurd(CHType, CHTerm)
  PTPair(CHTerm, CHTerm)
  PTFst(CHTerm)
  PTSnd(CHTerm)
  PTInl(CHType, CHTerm)
  PTInr(CHType, CHTerm)
  PTCase(CHTerm, CHTerm, CHTerm)
  PTLam(CHType, CHTerm)
  PTApp(CHTerm, CHTerm)
  PTDepLam(DomainSort, CHTerm)
  PTDepApp(CHTerm, ObjTerm)
  PTPack(ObjTerm, CHTerm, CHType)
  PTUnpack(CHTerm, CHTerm)
  PTRefl(DomainSort, ObjTerm)
  PTSquashBox(CHTerm)
  PTLetSquash(CHTerm, CHTerm)
}

///|
pub extend CHTerm with Eq::{equal, not_equal}

///|
pub extend CHTerm with @debug.Debug::{to_repr}

///|
/// Shift proof-variable De Bruijn indices >= `cutoff` by `delta`.
pub fn shift_ch_term(tm : CHTerm, delta : Int32, cutoff : Int32) -> CHTerm {
  if delta == 0 {
    return tm
  }
  match tm {
    PTVar(i) => if i >= cutoff { PTVar(i + delta) } else { tm }
    PTUnit | PTRefl(_, _) => tm
    PTAbsurd(ty, c) => PTAbsurd(ty, shift_ch_term(c, delta, cutoff))
    PTPair(a, b) =>
      PTPair(shift_ch_term(a, delta, cutoff), shift_ch_term(b, delta, cutoff))
    PTFst(p) => PTFst(shift_ch_term(p, delta, cutoff))
    PTSnd(p) => PTSnd(shift_ch_term(p, delta, cutoff))
    PTInl(rty, a) => PTInl(rty, shift_ch_term(a, delta, cutoff))
    PTInr(lty, b) => PTInr(lty, shift_ch_term(b, delta, cutoff))
    PTCase(s, l, r) =>
      PTCase(
        shift_ch_term(s, delta, cutoff),
        shift_ch_term(l, delta, cutoff + 1),
        shift_ch_term(r, delta, cutoff + 1),
      )
    PTLam(dom, body) => PTLam(dom, shift_ch_term(body, delta, cutoff + 1))
    PTApp(f, a) =>
      PTApp(shift_ch_term(f, delta, cutoff), shift_ch_term(a, delta, cutoff))
    PTDepLam(d, body) => PTDepLam(d, shift_ch_term(body, delta, cutoff))
    PTDepApp(f, o) => PTDepApp(shift_ch_term(f, delta, cutoff), o)
    PTPack(w, prf, ex_ty) => PTPack(w, shift_ch_term(prf, delta, cutoff), ex_ty)
    PTUnpack(ex, body) =>
      PTUnpack(
        shift_ch_term(ex, delta, cutoff),
        shift_ch_term(body, delta, cutoff + 1),
      )
    PTSquashBox(w) => PTSquashBox(shift_ch_term(w, delta, cutoff))
    PTLetSquash(sq, body) =>
      PTLetSquash(
        shift_ch_term(sq, delta, cutoff),
        shift_ch_term(body, delta, cutoff + 1),
      )
  }
}

///|
/// Substitute proof-variable `target` with `repl` in `CHTerm`.
pub fn subst_ch_term(tm : CHTerm, target : Int32, repl : CHTerm) -> CHTerm {
  match tm {
    PTVar(i) =>
      if i == target {
        shift_ch_term(repl, target, 0)
      } else if i > target {
        PTVar(i - 1)
      } else {
        tm
      }
    PTUnit | PTRefl(_, _) => tm
    PTAbsurd(ty, c) => PTAbsurd(ty, subst_ch_term(c, target, repl))
    PTPair(a, b) =>
      PTPair(subst_ch_term(a, target, repl), subst_ch_term(b, target, repl))
    PTFst(p) => PTFst(subst_ch_term(p, target, repl))
    PTSnd(p) => PTSnd(subst_ch_term(p, target, repl))
    PTInl(rty, a) => PTInl(rty, subst_ch_term(a, target, repl))
    PTInr(lty, b) => PTInr(lty, subst_ch_term(b, target, repl))
    PTCase(s, l, r) =>
      PTCase(
        subst_ch_term(s, target, repl),
        subst_ch_term(l, target + 1, repl),
        subst_ch_term(r, target + 1, repl),
      )
    PTLam(dom, body) => PTLam(dom, subst_ch_term(body, target + 1, repl))
    PTApp(f, a) =>
      PTApp(subst_ch_term(f, target, repl), subst_ch_term(a, target, repl))
    PTDepLam(d, body) => PTDepLam(d, subst_ch_term(body, target, repl))
    PTDepApp(f, o) => PTDepApp(subst_ch_term(f, target, repl), o)
    PTPack(w, prf, ex_ty) => PTPack(w, subst_ch_term(prf, target, repl), ex_ty)
    PTUnpack(ex, body) =>
      PTUnpack(
        subst_ch_term(ex, target, repl),
        subst_ch_term(body, target + 1, repl),
      )
    PTSquashBox(w) => PTSquashBox(subst_ch_term(w, target, repl))
    PTLetSquash(sq, body) =>
      PTLetSquash(
        subst_ch_term(sq, target, repl),
        subst_ch_term(body, target + 1, repl),
      )
  }
}

///|
/// Substitute object variable `target` with `repl` across `CHTerm`.
pub fn subst_ch_term_obj(tm : CHTerm, target : Int32, repl : ObjTerm) -> CHTerm {
  match tm {
    PTVar(_) | PTUnit => tm
    PTRefl(s, o) => PTRefl(s, subst_obj_term(o, target, repl))
    PTAbsurd(ty, c) =>
      PTAbsurd(
        subst_ch_type_obj(ty, target, repl),
        subst_ch_term_obj(c, target, repl),
      )
    PTPair(a, b) =>
      PTPair(
        subst_ch_term_obj(a, target, repl),
        subst_ch_term_obj(b, target, repl),
      )
    PTFst(p) => PTFst(subst_ch_term_obj(p, target, repl))
    PTSnd(p) => PTSnd(subst_ch_term_obj(p, target, repl))
    PTInl(rty, a) =>
      PTInl(
        subst_ch_type_obj(rty, target, repl),
        subst_ch_term_obj(a, target, repl),
      )
    PTInr(lty, b) =>
      PTInr(
        subst_ch_type_obj(lty, target, repl),
        subst_ch_term_obj(b, target, repl),
      )
    PTCase(s, l, r) =>
      PTCase(
        subst_ch_term_obj(s, target, repl),
        subst_ch_term_obj(l, target, repl),
        subst_ch_term_obj(r, target, repl),
      )
    PTLam(dom, body) =>
      PTLam(
        subst_ch_type_obj(dom, target, repl),
        subst_ch_term_obj(body, target, repl),
      )
    PTApp(f, a) =>
      PTApp(
        subst_ch_term_obj(f, target, repl),
        subst_ch_term_obj(a, target, repl),
      )
    PTDepLam(d, body) => PTDepLam(d, subst_ch_term_obj(body, target + 1, repl))
    PTDepApp(f, o) =>
      PTDepApp(
        subst_ch_term_obj(f, target, repl),
        subst_obj_term(o, target, repl),
      )
    PTPack(w, prf, ex_ty) =>
      PTPack(
        subst_obj_term(w, target, repl),
        subst_ch_term_obj(prf, target, repl),
        subst_ch_type_obj(ex_ty, target, repl),
      )
    PTUnpack(ex, body) =>
      PTUnpack(
        subst_ch_term_obj(ex, target, repl),
        subst_ch_term_obj(body, target + 1, repl),
      )
    PTSquashBox(w) => PTSquashBox(subst_ch_term_obj(w, target, repl))
    PTLetSquash(sq, body) =>
      PTLetSquash(
        subst_ch_term_obj(sq, target, repl),
        subst_ch_term_obj(body, target, repl),
      )
  }
}

///|
/// Verify BHK Constructive Proof Term `tm` in proof context `prf_ctx` (De Bruijn levels `0 .. n-1`).
pub fn infer_ch_term(
  prf_ctx : Array[CHType],
  tm : CHTerm,
) -> CHType raise LogicError {
  match tm {
    PTVar(idx) => {
      let pos = prf_ctx.length() - 1 - idx
      if idx < 0 || pos < 0 || pos >= prf_ctx.length() {
        raise LogicError::UnboundProofVar(idx)
      }
      prf_ctx[pos]
    }
    PTUnit => TUnit
    PTAbsurd(target_ty, contra) => {
      let c_ty = infer_ch_term(prf_ctx, contra)
      if c_ty != TEmpty {
        raise LogicError::ProofTypeMismatch(c_ty, TEmpty)
      }
      target_ty
    }
    PTPair(a, b) => TProd(infer_ch_term(prf_ctx, a), infer_ch_term(prf_ctx, b))
    PTFst(p) =>
      match infer_ch_term(prf_ctx, p) {
        TProd(a, _) => a
        other => raise LogicError::ExpectedProductProof(other)
      }
    PTSnd(p) =>
      match infer_ch_term(prf_ctx, p) {
        TProd(_, b) => b
        other => raise LogicError::ExpectedProductProof(other)
      }
    PTInl(right_ty, a) => TSum(infer_ch_term(prf_ctx, a), right_ty)
    PTInr(left_ty, b) => TSum(left_ty, infer_ch_term(prf_ctx, b))
    PTCase(scrut, on_l, on_r) =>
      match infer_ch_term(prf_ctx, scrut) {
        TSum(lty, rty) => {
          let ctx_l = prf_ctx.copy()
          ctx_l.push(lty)
          let ctx_r = prf_ctx.copy()
          ctx_r.push(rty)
          let res_l = infer_ch_term(ctx_l, on_l)
          let res_r = infer_ch_term(ctx_r, on_r)
          if res_l != res_r {
            raise LogicError::ProofTypeMismatch(res_l, res_r)
          }
          res_l
        }
        other => raise LogicError::ExpectedSumProof(other)
      }
    PTLam(dom, body) => {
      let ext = prf_ctx.copy()
      ext.push(dom)
      TArrow(dom, infer_ch_term(ext, body))
    }
    PTApp(f, arg) =>
      match infer_ch_term(prf_ctx, f) {
        TArrow(dom, cod) => {
          let arg_ty = infer_ch_term(prf_ctx, arg)
          if arg_ty != dom {
            raise LogicError::ProofTypeMismatch(arg_ty, dom)
          }
          cod
        }
        other => raise LogicError::ExpectedFunctionProof(other)
      }
    PTDepLam(d_sort, body) => {
      let shifted_ctx : Array[CHType] = []
      for ty in prf_ctx {
        shifted_ctx.push(shift_ch_type_obj(ty, 1, 0))
      }
      let body_ty = infer_ch_term(shifted_ctx, body)
      TPi("x", d_sort, body_ty)
    }
    PTDepApp(f, obj_arg) =>
      match infer_ch_term(prf_ctx, f) {
        TPi(_, _, body_ty) => subst_ch_type_obj(body_ty, 0, obj_arg)
        other => raise LogicError::ExpectedForallProof(other)
      }
    PTPack(witness, prf, ex_ty) =>
      match ex_ty {
        TSigma(_, _, body_ty) => {
          let expected_body = subst_ch_type_obj(body_ty, 0, witness)
          let actual = infer_ch_term(prf_ctx, prf)
          if actual != expected_body {
            raise LogicError::ProofTypeMismatch(actual, expected_body)
          }
          ex_ty
        }
        other => raise LogicError::ExpectedExistsProof(other)
      }
    PTUnpack(ex_tm, body) =>
      match infer_ch_term(prf_ctx, ex_tm) {
        TSigma(_, _, fam_ty) => {
          let shifted_ctx : Array[CHType] = []
          for ty in prf_ctx {
            shifted_ctx.push(shift_ch_type_obj(ty, 1, 0))
          }
          shifted_ctx.push(fam_ty)
          let res_ty = infer_ch_term(shifted_ctx, body)
          // Strengthen object variable 0 (standard existential side condition: x not free in conclusion)
          shift_ch_type_obj(res_ty, -1, 1)
        }
        other => raise LogicError::ExpectedExistsProof(other)
      }
    PTRefl(s, o) => TId(s, o, o)
    PTSquashBox(w) => TSquash(infer_ch_term(prf_ctx, w))
    PTLetSquash(sq, body) =>
      match infer_ch_term(prf_ctx, sq) {
        TSquash(inner_ty) => {
          let ext = prf_ctx.copy()
          ext.push(inner_ty)
          let res_ty = infer_ch_term(ext, body)
          // Theorem 4.1 (Squash Modality Elimination Guard): target MUST be proof-irrelevant!
          if !is_prop_irrelevant(res_ty) {
            raise LogicError::SquashEliminationIntoRelevantType(res_ty)
          }
          res_ty
        }
        other => raise LogicError::ProofTypeMismatch(other, TSquash(TUnit))
      }
  }
}

///|
/// Local Axiom (Prawitz Proof Normalization / Detour Elimination on `CHTerm`):
/// Eliminates all β-detours (`App(Lam, a)`, `Fst(Pair)`, `Snd(Pair)`, `Case(Inl/Inr)`,
/// `DepApp(DepLam)`, `Unpack(Pack)`, `LetSquash(SquashBox)`).
pub fn normalize_ch_term(tm : CHTerm) -> CHTerm {
  match tm {
    PTVar(_) | PTUnit | PTRefl(_, _) => tm
    PTAbsurd(ty, c) => PTAbsurd(ty, normalize_ch_term(c))
    PTPair(a, b) => PTPair(normalize_ch_term(a), normalize_ch_term(b))
    PTFst(p) =>
      match normalize_ch_term(p) {
        PTPair(a, _) => a
        np => PTFst(np)
      }
    PTSnd(p) =>
      match normalize_ch_term(p) {
        PTPair(_, b) => b
        np => PTSnd(np)
      }
    PTInl(ty, a) => PTInl(ty, normalize_ch_term(a))
    PTInr(ty, b) => PTInr(ty, normalize_ch_term(b))
    PTCase(s, l, r) =>
      match normalize_ch_term(s) {
        PTInl(_, v) => normalize_ch_term(subst_ch_term(l, 0, v))
        PTInr(_, v) => normalize_ch_term(subst_ch_term(r, 0, v))
        ns => PTCase(ns, normalize_ch_term(l), normalize_ch_term(r))
      }
    PTLam(dom, body) => PTLam(dom, normalize_ch_term(body))
    PTApp(f, a) => {
      let nf = normalize_ch_term(f)
      let na = normalize_ch_term(a)
      match nf {
        PTLam(_, body) => normalize_ch_term(subst_ch_term(body, 0, na))
        _ => PTApp(nf, na)
      }
    }
    PTDepLam(d, body) => PTDepLam(d, normalize_ch_term(body))
    PTDepApp(f, o) =>
      match normalize_ch_term(f) {
        PTDepLam(_, body) => normalize_ch_term(subst_ch_term_obj(body, 0, o))
        nf => PTDepApp(nf, o)
      }
    PTPack(w, p, ty) => PTPack(w, normalize_ch_term(p), ty)
    PTUnpack(ex, body) =>
      match normalize_ch_term(ex) {
        PTPack(w, prf, _) => {
          let body_inst = subst_ch_term_obj(body, 0, w)
          normalize_ch_term(subst_ch_term(body_inst, 0, prf))
        }
        nex => PTUnpack(nex, normalize_ch_term(body))
      }
    PTSquashBox(w) => PTSquashBox(normalize_ch_term(w))
    PTLetSquash(sq, body) =>
      match normalize_ch_term(sq) {
        PTSquashBox(w) => normalize_ch_term(subst_ch_term(body, 0, w))
        nsq => PTLetSquash(nsq, normalize_ch_term(body))
      }
  }
}
