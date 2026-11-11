///|
/// Module M10 (Part 2) — Quantitative Dependent Type Theory (`QTerm`) Bidirectional Resource Checker
/// & Certified 0-Grade Runtime Erasure (`erase_qtt_term` -> `RuntimeTerm`).

///|
#derive(Eq, Debug)
pub(all) enum QTerm {
  QVar(Int32)
  QUniv(Int32)
  QUnitTy
  QUnitVal
  QBoolTy
  QBoolVal(Bool)
  QIf(QTerm, QTerm, QTerm, QTerm)
  QPi(Grade, String, QTerm, QTerm)
  QLam(Grade, String, QTerm, QTerm)
  QApp(Grade, QTerm, QTerm)
  QSigma(Grade, String, QTerm, QTerm)
  QTensorPair(Grade, QTerm, QTerm, QTerm)
  QLetPair(Grade, QTerm, QTerm, QTerm)
  QWith(QTerm, QTerm)
  QWithPair(QTerm, QTerm)
  QWithFst(QTerm)
  QWithSnd(QTerm)
  QId(QTerm, QTerm, QTerm)
  QRefl(QTerm, QTerm)
}

///|
pub extend QTerm with Eq::{equal, not_equal}

///|
pub extend QTerm with @debug.Debug::{to_repr}

///|
/// Erased Untyped Runtime Lambda-Calculus Target (`0`-graded binders & arguments completely stripped!).
#derive(Eq, Debug)
pub(all) enum RuntimeTerm {
  RVar(Int32)
  RErasedBox
  RUnit
  RBool(Bool)
  RIf(RuntimeTerm, RuntimeTerm, RuntimeTerm)
  RLam(RuntimeTerm)
  RApp(RuntimeTerm, RuntimeTerm)
  RPair(RuntimeTerm, RuntimeTerm)
  RLetPair(RuntimeTerm, RuntimeTerm)
  RFst(RuntimeTerm)
  RSnd(RuntimeTerm)
}

///|
pub extend RuntimeTerm with Eq::{equal, not_equal}

///|
pub extend RuntimeTerm with @debug.Debug::{to_repr}

///|
pub fn shift_qterm(tm : QTerm, delta : Int32, cutoff : Int32) -> QTerm {
  if delta == 0 {
    return tm
  }
  match tm {
    QVar(i) => if i >= cutoff { QVar(i + delta) } else { tm }
    QUniv(_) | QUnitTy | QUnitVal | QBoolTy | QBoolVal(_) => tm
    QIf(sc, m, tb, fb) =>
      QIf(
        shift_qterm(sc, delta, cutoff),
        shift_qterm(m, delta, cutoff + 1),
        shift_qterm(tb, delta, cutoff),
        shift_qterm(fb, delta, cutoff),
      )
    QPi(g, x, a, b) =>
      QPi(
        g,
        x,
        shift_qterm(a, delta, cutoff),
        shift_qterm(b, delta, cutoff + 1),
      )
    QLam(g, x, a, b) =>
      QLam(
        g,
        x,
        shift_qterm(a, delta, cutoff),
        shift_qterm(b, delta, cutoff + 1),
      )
    QApp(g, f, a) =>
      QApp(g, shift_qterm(f, delta, cutoff), shift_qterm(a, delta, cutoff))
    QSigma(g, x, a, b) =>
      QSigma(
        g,
        x,
        shift_qterm(a, delta, cutoff),
        shift_qterm(b, delta, cutoff + 1),
      )
    QTensorPair(g, a, b, sig) =>
      QTensorPair(
        g,
        shift_qterm(a, delta, cutoff),
        shift_qterm(b, delta, cutoff),
        shift_qterm(sig, delta, cutoff),
      )
    QLetPair(g, sc, m, body) =>
      QLetPair(
        g,
        shift_qterm(sc, delta, cutoff),
        shift_qterm(m, delta, cutoff + 1),
        shift_qterm(body, delta, cutoff + 2),
      )
    QWith(a, b) =>
      QWith(shift_qterm(a, delta, cutoff), shift_qterm(b, delta, cutoff))
    QWithPair(a, b) =>
      QWithPair(shift_qterm(a, delta, cutoff), shift_qterm(b, delta, cutoff))
    QWithFst(p) => QWithFst(shift_qterm(p, delta, cutoff))
    QWithSnd(p) => QWithSnd(shift_qterm(p, delta, cutoff))
    QId(t, l, r) =>
      QId(
        shift_qterm(t, delta, cutoff),
        shift_qterm(l, delta, cutoff),
        shift_qterm(r, delta, cutoff),
      )
    QRefl(t, x) =>
      QRefl(shift_qterm(t, delta, cutoff), shift_qterm(x, delta, cutoff))
  }
}

///|
pub fn subst_qterm(tm : QTerm, target : Int32, repl : QTerm) -> QTerm {
  match tm {
    QVar(i) =>
      if i == target {
        repl
      } else if i > target {
        QVar(i - 1)
      } else {
        tm
      }
    QUniv(_) | QUnitTy | QUnitVal | QBoolTy | QBoolVal(_) => tm
    QIf(sc, m, tb, fb) =>
      QIf(
        subst_qterm(sc, target, repl),
        subst_qterm(m, target + 1, shift_qterm(repl, 1, 0)),
        subst_qterm(tb, target, repl),
        subst_qterm(fb, target, repl),
      )
    QPi(g, x, a, b) =>
      QPi(
        g,
        x,
        subst_qterm(a, target, repl),
        subst_qterm(b, target + 1, shift_qterm(repl, 1, 0)),
      )
    QLam(g, x, a, b) =>
      QLam(
        g,
        x,
        subst_qterm(a, target, repl),
        subst_qterm(b, target + 1, shift_qterm(repl, 1, 0)),
      )
    QApp(g, f, a) =>
      QApp(g, subst_qterm(f, target, repl), subst_qterm(a, target, repl))
    QSigma(g, x, a, b) =>
      QSigma(
        g,
        x,
        subst_qterm(a, target, repl),
        subst_qterm(b, target + 1, shift_qterm(repl, 1, 0)),
      )
    QTensorPair(g, a, b, sig) =>
      QTensorPair(
        g,
        subst_qterm(a, target, repl),
        subst_qterm(b, target, repl),
        subst_qterm(sig, target, repl),
      )
    QLetPair(g, sc, m, body) =>
      QLetPair(
        g,
        subst_qterm(sc, target, repl),
        subst_qterm(m, target + 1, shift_qterm(repl, 1, 0)),
        subst_qterm(body, target + 2, shift_qterm(repl, 2, 0)),
      )
    QWith(a, b) =>
      QWith(subst_qterm(a, target, repl), subst_qterm(b, target, repl))
    QWithPair(a, b) =>
      QWithPair(subst_qterm(a, target, repl), subst_qterm(b, target, repl))
    QWithFst(p) => QWithFst(subst_qterm(p, target, repl))
    QWithSnd(p) => QWithSnd(subst_qterm(p, target, repl))
    QId(t, l, r) =>
      QId(
        subst_qterm(t, target, repl),
        subst_qterm(l, target, repl),
        subst_qterm(r, target, repl),
      )
    QRefl(t, x) =>
      QRefl(subst_qterm(t, target, repl), subst_qterm(x, target, repl))
  }
}

///|
/// Head β-Normalizer for `QTerm` Type Conversion Checking.
pub fn normalize_qterm(tm : QTerm) -> QTerm {
  match tm {
    QVar(_) | QUniv(_) | QUnitTy | QUnitVal | QBoolTy | QBoolVal(_) => tm
    QPi(g, x, a, b) => QPi(g, x, normalize_qterm(a), normalize_qterm(b))
    QLam(g, x, a, b) => QLam(g, x, normalize_qterm(a), normalize_qterm(b))
    QApp(g, f, a) => {
      let nf = normalize_qterm(f)
      let na = normalize_qterm(a)
      match nf {
        QLam(_, _, _, body) => normalize_qterm(subst_qterm(body, 0, na))
        _ => QApp(g, nf, na)
      }
    }
    QIf(sc, m, tb, fb) => {
      let nsc = normalize_qterm(sc)
      match nsc {
        QBoolVal(true) => normalize_qterm(tb)
        QBoolVal(false) => normalize_qterm(fb)
        _ =>
          QIf(nsc, normalize_qterm(m), normalize_qterm(tb), normalize_qterm(fb))
      }
    }
    QSigma(g, x, a, b) => QSigma(g, x, normalize_qterm(a), normalize_qterm(b))
    QTensorPair(g, a, b, s) =>
      QTensorPair(g, normalize_qterm(a), normalize_qterm(b), normalize_qterm(s))
    QLetPair(g, sc, m, body) => {
      let nsc = normalize_qterm(sc)
      match nsc {
        QTensorPair(_, va, vb, _) => {
          let sub1 = subst_qterm(body, 0, vb)
          let sub2 = subst_qterm(sub1, 0, va)
          normalize_qterm(sub2)
        }
        _ => QLetPair(g, nsc, normalize_qterm(m), normalize_qterm(body))
      }
    }
    QWith(a, b) => QWith(normalize_qterm(a), normalize_qterm(b))
    QWithPair(a, b) => QWithPair(normalize_qterm(a), normalize_qterm(b))
    QWithFst(p) =>
      match normalize_qterm(p) {
        QWithPair(a, _) => a
        np => QWithFst(np)
      }
    QWithSnd(p) =>
      match normalize_qterm(p) {
        QWithPair(_, b) => b
        np => QWithSnd(np)
      }
    QId(t, l, r) =>
      QId(normalize_qterm(t), normalize_qterm(l), normalize_qterm(r))
    QRefl(t, x) => QRefl(normalize_qterm(t), normalize_qterm(x))
  }
}

///|
/// Graded Context Entry `(name, declared_grade, ty)` (outermost at index `0`, innermost at `len - 1`).
#derive(Eq, Debug)
pub(all) struct QCtxEntry {
  name : String
  grade : Grade
  ty : QTerm
}

///|
pub extend QCtxEntry with Eq::{equal, not_equal}

///|
pub extend QCtxEntry with @debug.Debug::{to_repr}

///|
/// Rescale all context entries to `GOmega` during 0-grade type-formation checking (`0 · Γ ⊢ A Type`):
/// In QTT (McBride 2016; Atkey 2018), types live at runtime multiplicity `0`, so ANY variable in `Γ`
/// (even `0`-graded or `1`-graded!) may be referenced freely inside a type, while the returned
/// runtime usage vector of `check_qtype` is `0 · u = UsageVec64::zero()`!
fn unrestricted_type_ctx(ctx : Array[QCtxEntry]) -> Array[QCtxEntry] {
  let out : Array[QCtxEntry] = []
  for e in ctx {
    out.push({ name: e.name, grade: GOmega, ty: e.ty, })
  }
  out
}

///|
pub fn check_qtype(ctx : Array[QCtxEntry], ty : QTerm) -> Int32 raise QTTError {
  let ty_ctx = unrestricted_type_ctx(ctx)
  let (sort_tm, _) = synth_qterm_raw(ty_ctx, ty)
  match normalize_qterm(sort_tm) {
    QUniv(l) => l
    other => raise QTTError::ExpectedTypeSort(other)
  }
}

///|
/// Synthesize `(inferred_type, runtime_usage_vec)` for `tm` under `ctx`,
/// WITHOUT yet checking global outer-context subsumption (which `check_top_qterm` also enforces!).
/// Every binder (`QLam`, `QLetPair`) immediately enforces local resource subsumption on its bound variable(s)!
pub fn synth_qterm_raw(
  ctx : Array[QCtxEntry],
  tm : QTerm,
) -> (QTerm, UsageVec64) raise QTTError {
  let d = ctx.length()
  match tm {
    QVar(idx) => {
      if idx < 0 || idx >= d {
        raise QTTError::UnboundQVar(idx)
      }
      let lvl = d - 1 - idx
      let entry = ctx[lvl]
      if entry.grade == GZero {
        raise QTTError::ZeroGradeVariableUsedAtRuntime(idx)
      }
      let shifted_ty = shift_qterm(entry.ty, idx + 1, 0)
      (shifted_ty, UsageVec64::singleton(lvl, GOne))
    }
    QUniv(l) => (QUniv(l + 1), UsageVec64::zero())
    QUnitTy | QBoolTy => (QUniv(0), UsageVec64::zero())
    QUnitVal => (QUnitTy, UsageVec64::zero())
    QBoolVal(_) => (QBoolTy, UsageVec64::zero())
    QPi(_, x, a, b) | QSigma(_, x, a, b) => {
      let l1 = check_qtype(ctx, a)
      let ext = ctx.copy()
      ext.push({ name: x, grade: GOmega, ty: a, })
      let l2 = check_qtype(ext, b)
      let lub = if l1 >= l2 { l1 } else { l2 }
      (QUniv(lub), UsageVec64::zero())
    }
    QWith(a, b) => {
      let l1 = check_qtype(ctx, a)
      let l2 = check_qtype(ctx, b)
      let lub = if l1 >= l2 { l1 } else { l2 }
      (QUniv(lub), UsageVec64::zero())
    }
    QId(t, l, r) => {
      let lvl = check_qtype(ctx, t)
      let ty_ctx = unrestricted_type_ctx(ctx)
      let _ = check_qterm_raw(ty_ctx, l, t)
      let _ = check_qterm_raw(ty_ctx, r, t)
      (QUniv(lvl), UsageVec64::zero())
    }
    QLam(g, x, a, body) => {
      let _ = check_qtype(ctx, a)
      let ext = ctx.copy()
      ext.push({ name: x, grade: g, ty: a, })
      let (cod_ty, body_u) = synth_qterm_raw(ext, body)
      let actual_x = body_u.get(d)
      if !actual_x.subsumed_by(g) {
        raise QTTError::ResourceSubsumptionViolation(x, actual_x, g)
      }
      (QPi(g, x, a, cod_ty), body_u.clear_slot(d))
    }
    QApp(g, f, arg) => {
      let (f_ty, u_f) = synth_qterm_raw(ctx, f)
      match normalize_qterm(f_ty) {
        QPi(pi_g, _, dom, cod) => {
          if g != pi_g {
            raise QTTError::GradeAnnotationMismatch(g, pi_g)
          }
          let u_arg = if g == GZero {
            let ty_ctx = unrestricted_type_ctx(ctx)
            let _ = check_qterm_raw(ty_ctx, arg, dom)
            UsageVec64::zero()
          } else {
            let ua = check_qterm_raw(ctx, arg, dom)
            ua.scale(g)
          }
          (subst_qterm(cod, 0, arg), u_f.add(u_arg))
        }
        other => raise QTTError::ExpectedGradedPi(other)
      }
    }
    QTensorPair(g, a, b, whole_sig) => {
      let _ = check_qtype(ctx, whole_sig)
      match normalize_qterm(whole_sig) {
        QSigma(sig_g, _, fst_ty, snd_ty) => {
          if g != sig_g {
            raise QTTError::GradeAnnotationMismatch(g, sig_g)
          }
          let u_a = if g == GZero {
            let ty_ctx = unrestricted_type_ctx(ctx)
            let _ = check_qterm_raw(ty_ctx, a, fst_ty)
            UsageVec64::zero()
          } else {
            check_qterm_raw(ctx, a, fst_ty).scale(g)
          }
          let inst_snd = subst_qterm(snd_ty, 0, a)
          let u_b = check_qterm_raw(ctx, b, inst_snd)
          (whole_sig, u_a.add(u_b))
        }
        other => raise QTTError::ExpectedGradedSigma(other)
      }
    }
    QLetPair(elim_g, scrut, motive, body) => {
      let (sc_ty, u_sc_raw) = synth_qterm_raw(ctx, scrut)
      match normalize_qterm(sc_ty) {
        QSigma(pi_g, x_name, fst_ty, snd_ty) => {
          let ext_m = ctx.copy()
          ext_m.push({ name: "p", grade: GOmega, ty: sc_ty, })
          let _ = check_qtype(ext_m, motive)
          let x_grade = elim_g.mul(pi_g)
          let ext_b = ctx.copy()
          ext_b.push({ name: x_name, grade: x_grade, ty: fst_ty, })
          ext_b.push({ name: "y", grade: elim_g, ty: snd_ty, })
          // Expected body type is `motive[p := (x, y)]`:
          let pair_var = QTensorPair(
            pi_g,
            QVar(1),
            QVar(0),
            shift_qterm(sc_ty, 2, 0),
          )
          let m_shifted = shift_qterm(motive, 2, 1)
          let body_expected = subst_qterm(m_shifted, 0, pair_var)
          let u_body = check_qterm_raw(ext_b, body, body_expected)
          let act_x = u_body.get(d)
          let act_y = u_body.get(d + 1)
          if !act_x.subsumed_by(x_grade) {
            raise QTTError::ResourceSubsumptionViolation(x_name, act_x, x_grade)
          }
          if !act_y.subsumed_by(elim_g) {
            raise QTTError::ResourceSubsumptionViolation("y", act_y, elim_g)
          }
          let u_clean = u_body.clear_slot(d).clear_slot(d + 1)
          let u_sc = u_sc_raw.scale(elim_g)
          (subst_qterm(motive, 0, scrut), u_sc.add(u_clean))
        }
        other => raise QTTError::ExpectedGradedSigma(other)
      }
    }
    QWithPair(a, b) => {
      let (ta, ua) = synth_qterm_raw(ctx, a)
      let (tb, ub) = synth_qterm_raw(ctx, b)
      (QWith(ta, tb), ua.additive_join(ub))
    }
    QWithFst(p) => {
      let (tp, up) = synth_qterm_raw(ctx, p)
      match normalize_qterm(tp) {
        QWith(ta, _) => (ta, up)
        other => raise QTTError::ExpectedAdditiveWith(other)
      }
    }
    QWithSnd(p) => {
      let (tp, up) = synth_qterm_raw(ctx, p)
      match normalize_qterm(tp) {
        QWith(_, tb) => (tb, up)
        other => raise QTTError::ExpectedAdditiveWith(other)
      }
    }
    QIf(sc, motive, tb, fb) => {
      let u_sc = check_qterm_raw(ctx, sc, QBoolTy)
      let ext_m = ctx.copy()
      ext_m.push({ name: "b", grade: GOmega, ty: QBoolTy, })
      let _ = check_qtype(ext_m, motive)
      let u_t = check_qterm_raw(ctx, tb, subst_qterm(motive, 0, QBoolVal(true)))
      let u_f = check_qterm_raw(
        ctx,
        fb,
        subst_qterm(motive, 0, QBoolVal(false)),
      )
      (subst_qterm(motive, 0, sc), u_sc.add(u_t.additive_join(u_f)))
    }
    QRefl(t, x) => {
      let _ = check_qtype(ctx, t)
      let ty_ctx = unrestricted_type_ctx(ctx)
      let _ = check_qterm_raw(ty_ctx, x, t)
      (QId(t, x, x), UsageVec64::zero())
    }
  }
}

///|
pub fn check_qterm_raw(
  ctx : Array[QCtxEntry],
  tm : QTerm,
  expected : QTerm,
) -> UsageVec64 raise QTTError {
  let (inferred, u) = synth_qterm_raw(ctx, tm)
  let n_inf = normalize_qterm(inferred)
  let n_exp = normalize_qterm(expected)
  if n_inf != n_exp {
    raise QTTError::QTypeMismatch(n_inf, n_exp)
  }
  u
}

///|
/// Top-Level Certified Quantitative Judgment `Γ ⊢ tm : ty`!
/// Synthesizes `(ty, u)` AND verifies that EVERY variable `l` in `Γ` satisfies `u[l] ≼ Γ[l].grade`!
pub fn verify_qtt_judgment(
  ctx : Array[QCtxEntry],
  tm : QTerm,
) -> (QTerm, UsageVec64) raise QTTError {
  let (ty, u) = synth_qterm_raw(ctx, tm)
  for l = 0; l < ctx.length(); l = l + 1 {
    let act = u.get(l)
    let decl = ctx[l].grade
    if !act.subsumed_by(decl) {
      raise QTTError::ResourceSubsumptionViolation(ctx[l].name, act, decl)
    }
  }
  (ty, u)
}

///|
fn subst_runtime(
  rt : RuntimeTerm,
  target : Int32,
  repl : RuntimeTerm,
) -> RuntimeTerm {
  match rt {
    RVar(i) =>
      if i == target {
        repl
      } else if i > target {
        RVar(i - 1)
      } else {
        rt
      }
    RErasedBox | RUnit | RBool(_) => rt
    RIf(c, t, f) =>
      RIf(
        subst_runtime(c, target, repl),
        subst_runtime(t, target, repl),
        subst_runtime(f, target, repl),
      )
    RLam(b) => RLam(subst_runtime(b, target + 1, repl))
    RApp(f, a) =>
      RApp(subst_runtime(f, target, repl), subst_runtime(a, target, repl))
    RPair(a, b) =>
      RPair(subst_runtime(a, target, repl), subst_runtime(b, target, repl))
    RLetPair(s, b) =>
      RLetPair(
        subst_runtime(s, target, repl),
        subst_runtime(b, target + 2, repl),
      )
    RFst(p) => RFst(subst_runtime(p, target, repl))
    RSnd(p) => RSnd(subst_runtime(p, target, repl))
  }
}

///|
/// Theorem 10.3 (Certified 0-Grade Runtime Erasure):
/// Erases ALL types, `0`-graded abstractions, `0`-graded applications, `0`-graded tensor components,
/// and equality proofs (`QRefl` -> `RUnit`), yielding a lean runtime program!
pub fn erase_qtt_term(tm : QTerm) -> RuntimeTerm {
  match tm {
    QVar(i) => RVar(i)
    QUniv(_)
    | QUnitTy
    | QBoolTy
    | QPi(_, _, _, _)
    | QSigma(_, _, _, _)
    | QWith(_, _)
    | QId(_, _, _) => RErasedBox
    QUnitVal | QRefl(_, _) => RUnit
    QBoolVal(b) => RBool(b)
    QIf(sc, _, tb, fb) =>
      RIf(erase_qtt_term(sc), erase_qtt_term(tb), erase_qtt_term(fb))
    QLam(g, _, _, body) => {
      let eb = erase_qtt_term(body)
      if g == GZero {
        subst_runtime(eb, 0, RErasedBox)
      } else {
        RLam(eb)
      }
    }
    QApp(g, f, a) => {
      let ef = erase_qtt_term(f)
      if g == GZero {
        ef
      } else {
        RApp(ef, erase_qtt_term(a))
      }
    }
    QTensorPair(g, a, b, _) =>
      if g == GZero {
        RPair(RErasedBox, erase_qtt_term(b))
      } else {
        RPair(erase_qtt_term(a), erase_qtt_term(b))
      }
    QLetPair(_, sc, _, body) =>
      RLetPair(erase_qtt_term(sc), erase_qtt_term(body))
    QWithPair(a, b) => RPair(erase_qtt_term(a), erase_qtt_term(b))
    QWithFst(p) => RFst(erase_qtt_term(p))
    QWithSnd(p) => RSnd(erase_qtt_term(p))
  }
}
