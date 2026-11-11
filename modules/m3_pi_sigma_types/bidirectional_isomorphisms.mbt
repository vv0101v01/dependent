///|
/// Module M3 — Bidirectional Judgment Kernel (Γ ⊢ A type, Γ ⊢ t ⇒ A, Γ ⊢ t ⇐ A)
/// + Dependent Currying Isomorphism (Π-Σ Adjunction)
/// + Dependent Skolem / Choice Isomorphism (Trotta-Weinberger-de Paiva 2024).

///|
pub(all) struct JudgmentCtx {
  names : Array[String]
  /// Semantic types indexed by De Bruijn level `0 .. depth - 1`
  types : Array[Val]
  /// Semantic values for context reflection (`↑Γ`: neutral variables or local defs)
  env : Array[Val]
  allow_cumul : Bool
}

///|
pub fn JudgmentCtx::empty(allow_cumul : Bool) -> JudgmentCtx {
  { names: [], types: [], env: [], allow_cumul, }
}

///|
pub fn JudgmentCtx::depth(self : JudgmentCtx) -> Int32 {
  self.types.length()
}

///|
/// Context reflection `↑(Γ, x : A)`: extends semantic environment with fresh neutral variable at `|Γ|`.
pub fn JudgmentCtx::push_var(
  self : JudgmentCtx,
  name : String,
  vty : Val,
) -> JudgmentCtx {
  let lvl = self.types.length()
  let names = self.names.copy()
  let types = self.types.copy()
  let env = self.env.copy()
  names.push(name)
  types.push(vty)
  env.push(fresh_neutral_var(lvl, vty))
  { names, types, env, allow_cumul: self.allow_cumul, }
}

///|
/// Normalize a well-typed term `tm` of syntactic type `ty` in `ctx` to its βη-canonical `CoreTm`.
pub fn JudgmentCtx::normalize(
  self : JudgmentCtx,
  tm : CoreTm,
  ty : CoreTm,
) -> CoreTm {
  let vty = eval_tm(self.env, ty)
  let vtm = eval_tm(self.env, tm)
  quote_val(self.depth(), vty, vtm)
}

///|
/// Check Type Formation Judgment `Γ ⊢ A type` and evaluate `A` to semantic type `Val`,
/// also synthesizing its minimal universe smallness level `i` (`Γ ⊢ A small_i`).
pub fn check_is_type(
  ctx : JudgmentCtx,
  ty_expr : CoreTm,
) -> (Val, Int32) raise TypeTheoryError {
  match ty_expr {
    CUniv(i) =>
      if i < 0 {
        raise TypeTheoryError::ExpectedTypeForm("negative universe")
      } else {
        (VUniv(i), i + 1)
      }
    CProp => (VProp, 0)
    CUnit => (VUnit, 0)
    CNat => (VNat, 0)
    CSmallDec(i, code_tm) => {
      check_term(ctx, code_tm, VUniv(i))
      (eval_tm(ctx.env, ty_expr), i)
    }
    CPi(x, dom_tm, cod_tm) => {
      let (v_dom, l_dom) = check_is_type(ctx, dom_tm)
      let ctx_ext = ctx.push_var(x, v_dom)
      let (_, l_cod) = check_is_type(ctx_ext, cod_tm)
      let lub = if l_dom >= l_cod { l_dom } else { l_cod }
      (eval_tm(ctx.env, ty_expr), lub)
    }
    CSigma(x, fst_tm, snd_tm) => {
      let (v_fst, l_fst) = check_is_type(ctx, fst_tm)
      let ctx_ext = ctx.push_var(x, v_fst)
      let (_, l_snd) = check_is_type(ctx_ext, snd_tm)
      let lub = if l_fst >= l_snd { l_fst } else { l_snd }
      (eval_tm(ctx.env, ty_expr), lub)
    }
    CId(a_tm, lhs_tm, rhs_tm) => {
      let (v_a, l_a) = check_is_type(ctx, a_tm)
      check_term(ctx, lhs_tm, v_a)
      check_term(ctx, rhs_tm, v_a)
      (eval_tm(ctx.env, ty_expr), l_a)
    }
    CSquash(a_tm) => {
      let _ = check_is_type(ctx, a_tm)
      (eval_tm(ctx.env, ty_expr), 0)
    }
    other => {
      // Allow terms inhabiting U_i or Prop to act Russell-style when decoded implicitly
      let inf_ty = synth_term(ctx, other)
      match inf_ty {
        VUniv(i) => (eval_tm(ctx.env, other), i)
        VProp => (eval_tm(ctx.env, other), 0)
        _ => raise TypeTheoryError::ExpectedTypeForm("\{other}")
      }
    }
  }
}

///|
fn check_subsumption(
  ctx : JudgmentCtx,
  inferred : Val,
  expected : Val,
) -> Unit raise TypeTheoryError {
  let d = ctx.depth()
  if conv_ty(d, inferred, expected) {
    return ()
  }
  match (inferred, expected) {
    (VUniv(i), VUniv(j)) =>
      if ctx.allow_cumul && i <= j {
        return ()
      } else {
        raise TypeTheoryError::UniverseCumulViolation(i, j)
      }
    (VSquash(_), VProp) => ()
    _ =>
      raise TypeTheoryError::ConversionMismatch(
        quote_ty(d, inferred),
        quote_ty(d, expected),
      )
  }
}

///|
/// Bidirectional Synthesis Judgment `Γ ⊢ tm ⇒ A`.
pub fn synth_term(ctx : JudgmentCtx, tm : CoreTm) -> Val raise TypeTheoryError {
  match tm {
    CVar(idx) => {
      let d = ctx.depth()
      let lvl = d - 1 - idx
      if idx < 0 || lvl < 0 || lvl >= d {
        raise TypeTheoryError::UnboundIndex(idx, d)
      }
      ctx.types[lvl]
    }
    CUniv(i) => VUniv(i + 1)
    CProp => VUniv(0)
    CUnit => VUniv(0)
    CStar => VUnit
    CNat => VUniv(0)
    CZero => VNat
    CSucc(n) => {
      check_term(ctx, n, VNat)
      VNat
    }
    CSmallEnc(target_lvl, a_tm) => {
      let (_, min_lvl) = check_is_type(ctx, a_tm)
      if ctx.allow_cumul {
        if min_lvl > target_lvl {
          raise TypeTheoryError::ExpectedUnivCode(target_lvl)
        }
      } else if min_lvl != target_lvl {
        raise TypeTheoryError::UniverseCumulViolation(min_lvl, target_lvl)
      }
      VUniv(target_lvl)
    }
    CSmallDec(lvl, m_tm) => {
      check_term(ctx, m_tm, VUniv(lvl))
      VUniv(lvl + 1)
    }
    CPi(x, dom_tm, cod_tm) => {
      let (v_dom, l_dom) = check_is_type(ctx, dom_tm)
      let (_, l_cod) = check_is_type(ctx.push_var(x, v_dom), cod_tm)
      let lub = if l_dom >= l_cod { l_dom } else { l_cod }
      VUniv(lub)
    }
    CLam(x, dom_tm, body_tm) => {
      let (v_dom, _) = check_is_type(ctx, dom_tm)
      let ext = ctx.push_var(x, v_dom)
      let v_cod = synth_term(ext, body_tm)
      let q_cod = quote_ty(ext.depth(), v_cod)
      VPi(x, v_dom, { env: ctx.env.copy(), body: q_cod, })
    }
    CApp(fn_tm, arg_tm) => {
      let fn_ty = synth_term(ctx, fn_tm)
      match fn_ty {
        VPi(_, dom, cod_clos) => {
          check_term(ctx, arg_tm, dom)
          let v_arg = eval_tm(ctx.env, arg_tm)
          eval_clos(cod_clos, v_arg)
        }
        other =>
          raise TypeTheoryError::ExpectedPiType(
            "\{quote_ty(ctx.depth(), other)}",
          )
      }
    }
    CSigma(x, fst_tm, snd_tm) => {
      let (v_fst, l_fst) = check_is_type(ctx, fst_tm)
      let (_, l_snd) = check_is_type(ctx.push_var(x, v_fst), snd_tm)
      let lub = if l_fst >= l_snd { l_fst } else { l_snd }
      VUniv(lub)
    }
    CFst(p_tm) => {
      let p_ty = synth_term(ctx, p_tm)
      match p_ty {
        VSigma(_, fst_t, _) => fst_t
        other =>
          raise TypeTheoryError::ExpectedSigmaType(
            "\{quote_ty(ctx.depth(), other)}",
          )
      }
    }
    CSnd(p_tm) => {
      let p_ty = synth_term(ctx, p_tm)
      match p_ty {
        VSigma(_, _, snd_clos) => {
          let vp = eval_tm(ctx.env, p_tm)
          eval_clos(snd_clos, fst_val(vp))
        }
        other =>
          raise TypeTheoryError::ExpectedSigmaType(
            "\{quote_ty(ctx.depth(), other)}",
          )
      }
    }
    CNatRec(mot_tm, base_tm, step_tm, target_tm) => {
      let ext_n = ctx.push_var("n", VNat)
      let _ = check_is_type(ext_n, mot_tm)
      let mot_clos : Clos = { env: ctx.env.copy(), body: mot_tm, }
      check_term(ctx, base_tm, eval_clos(mot_clos, VZero))
      let ext_k = ctx.push_var("k", VNat)
      let k_var = fresh_neutral_var(ctx.depth(), VNat)
      let ih_ty = eval_clos(mot_clos, k_var)
      let ext_ih = ext_k.push_var("ih", ih_ty)
      check_term(ext_ih, step_tm, eval_clos(mot_clos, VSucc(k_var)))
      check_term(ctx, target_tm, VNat)
      let v_target = eval_tm(ctx.env, target_tm)
      eval_clos(mot_clos, v_target)
    }
    CId(a_tm, l_tm, r_tm) => {
      let (v_a, l_a) = check_is_type(ctx, a_tm)
      check_term(ctx, l_tm, v_a)
      check_term(ctx, r_tm, v_a)
      VUniv(l_a)
    }
    CJ(a_tm, lhs_tm, mot_tm, rf_tm, rhs_tm, eq_tm) => {
      let (v_a, _) = check_is_type(ctx, a_tm)
      check_term(ctx, lhs_tm, v_a)
      let v_lhs = eval_tm(ctx.env, lhs_tm)
      let ext_y = ctx.push_var("y", v_a)
      let y_var = fresh_neutral_var(ctx.depth(), v_a)
      let ext_p = ext_y.push_var("p", VId(v_a, v_lhs, y_var))
      let _ = check_is_type(ext_p, mot_tm)
      let mot_clos : Clos = { env: ctx.env.copy(), body: mot_tm, }
      check_term(ctx, rf_tm, eval_clos2(mot_clos, v_lhs, VRefl(v_lhs)))
      check_term(ctx, rhs_tm, v_a)
      let v_rhs = eval_tm(ctx.env, rhs_tm)
      check_term(ctx, eq_tm, VId(v_a, v_lhs, v_rhs))
      let v_eq = eval_tm(ctx.env, eq_tm)
      eval_clos2(mot_clos, v_rhs, v_eq)
    }
    CSquash(a_tm) => {
      let _ = check_is_type(ctx, a_tm)
      VProp
    }
    CBoxProof(w_tm) => {
      let w_ty = synth_term(ctx, w_tm)
      VSquash(w_ty)
    }
    CAnn(e_tm, ty_tm) => {
      let (v_ty, _) = check_is_type(ctx, ty_tm)
      check_term(ctx, e_tm, v_ty)
      v_ty
    }
    CPair(a_tm, b_tm) => {
      let va = synth_term(ctx, a_tm)
      let vb = synth_term(ctx, b_tm)
      let qb_weaken = shift_core(quote_ty(ctx.depth(), vb), 1, 0)
      VSigma("_", va, { env: ctx.env.copy(), body: qb_weaken, })
    }
    CRefl(_) => raise TypeTheoryError::CannotSynthesizeUnannotated("CRefl")
  }
}

///|
/// Bidirectional Checking Judgment `Γ ⊢ tm ⇐ expected`.
pub fn check_term(
  ctx : JudgmentCtx,
  tm : CoreTm,
  expected : Val,
) -> Unit raise TypeTheoryError {
  match (tm, expected) {
    (CLam(x, dom_tm, body_tm), VPi(_, exp_dom, cod_clos)) => {
      let (v_dom, _) = check_is_type(ctx, dom_tm)
      check_subsumption(ctx, exp_dom, v_dom)
      let ext = ctx.push_var(x, exp_dom)
      let arg_var = fresh_neutral_var(ctx.depth(), exp_dom)
      check_term(ext, body_tm, eval_clos(cod_clos, arg_var))
    }
    (CPair(fst_tm, snd_tm), VSigma(_, fst_ty, snd_clos)) => {
      check_term(ctx, fst_tm, fst_ty)
      let v_fst = eval_tm(ctx.env, fst_tm)
      check_term(ctx, snd_tm, eval_clos(snd_clos, v_fst))
    }
    (CRefl(x_tm), VId(ty, lhs, rhs)) => {
      check_term(ctx, x_tm, ty)
      let vx = eval_tm(ctx.env, x_tm)
      if !conv_val(ctx.depth(), ty, vx, lhs) {
        raise TypeTheoryError::ExpectedIdType
      }
      if !conv_val(ctx.depth(), ty, vx, rhs) {
        raise TypeTheoryError::ExpectedIdType
      }
    }
    (CBoxProof(w_tm), VSquash(inner_ty)) => check_term(ctx, w_tm, inner_ty)
    (other, exp) => {
      let inf = synth_term(ctx, other)
      check_subsumption(ctx, inf, exp)
    }
  }
}

///|
/// Substitute De Bruijn index 0 in `body` with `arg` (syntactic helper for universal combinators).
fn subst0_core(body : CoreTm, arg : CoreTm) -> CoreTm {
  subst_at_core(body, 0, arg)
}

///|
fn subst_at_core(tm : CoreTm, target : Int32, arg : CoreTm) -> CoreTm {
  match tm {
    CVar(i) =>
      if i == target {
        shift_core(arg, target, 0)
      } else if i > target {
        CVar(i - 1)
      } else {
        tm
      }
    CUniv(_) | CProp | CUnit | CStar | CNat | CZero => tm
    CSmallEnc(l, a) => CSmallEnc(l, subst_at_core(a, target, arg))
    CSmallDec(l, m) => CSmallDec(l, subst_at_core(m, target, arg))
    CPi(x, a, b) =>
      CPi(x, subst_at_core(a, target, arg), subst_at_core(b, target + 1, arg))
    CLam(x, a, b) =>
      CLam(x, subst_at_core(a, target, arg), subst_at_core(b, target + 1, arg))
    CApp(f, a) =>
      CApp(subst_at_core(f, target, arg), subst_at_core(a, target, arg))
    CSigma(x, a, b) =>
      CSigma(
        x,
        subst_at_core(a, target, arg),
        subst_at_core(b, target + 1, arg),
      )
    CPair(a, b) =>
      CPair(subst_at_core(a, target, arg), subst_at_core(b, target, arg))
    CFst(p) => CFst(subst_at_core(p, target, arg))
    CSnd(p) => CSnd(subst_at_core(p, target, arg))
    CSucc(n) => CSucc(subst_at_core(n, target, arg))
    CNatRec(m, z, s, n) =>
      CNatRec(
        subst_at_core(m, target + 1, arg),
        subst_at_core(z, target, arg),
        subst_at_core(s, target + 2, arg),
        subst_at_core(n, target, arg),
      )
    CId(t, l, r) =>
      CId(
        subst_at_core(t, target, arg),
        subst_at_core(l, target, arg),
        subst_at_core(r, target, arg),
      )
    CRefl(x) => CRefl(subst_at_core(x, target, arg))
    CJ(t, l, m, rf, r, p) =>
      CJ(
        subst_at_core(t, target, arg),
        subst_at_core(l, target, arg),
        subst_at_core(m, target + 2, arg),
        subst_at_core(rf, target, arg),
        subst_at_core(r, target, arg),
        subst_at_core(p, target, arg),
      )
    CSquash(a) => CSquash(subst_at_core(a, target, arg))
    CBoxProof(a) => CBoxProof(subst_at_core(a, target, arg))
    CAnn(e, t) =>
      CAnn(subst_at_core(e, target, arg), subst_at_core(t, target, arg))
  }
}

///|
/// Theorem 3.2 (Dependent Currying Adjointness `Σ ⊣ Δ ⊣ Π`):
/// Source Type: `Π(p : Σ(x:A). B(x)). C(p)`
/// Target Type: `Π(x:A). Π(y:B(x)). C(<x, y>)`
pub fn dep_uncurried_type(a : CoreTm, b : CoreTm, c_over_p : CoreTm) -> CoreTm {
  CPi("p", CSigma("x", a, b), c_over_p)
}

///|
pub fn dep_curried_type(a : CoreTm, b : CoreTm, c_over_p : CoreTm) -> CoreTm {
  // Inside `x : A, y : B(x)`: `x` is `#1`, `y` is `#0`.
  // Shift `c_over_p` outer vars by +2 (cutoff 1), then replace `p` (`#0`) by `<#1, #0>`:
  let c_weaken = shift_core(c_over_p, 2, 1)
  let c_xy = subst0_core(c_weaken, CPair(CVar(1), CVar(0)))
  CPi("x", a, CPi("y", b, c_xy))
}

///|
/// Forward Dependent Currying Transformer: `f ↦ λ(x:A). λ(y:B(x)). f <x, y>`.
pub fn dep_curry_term(a : CoreTm, b : CoreTm, f_tm : CoreTm) -> CoreTm {
  let f_shifted = shift_core(f_tm, 2, 0)
  CLam("x", a, CLam("y", b, CApp(f_shifted, CPair(CVar(1), CVar(0)))))
}

///|
/// Inverse Dependent Uncurrying Transformer: `g ↦ λ(p : Σ(x:A).B(x)). g (fst p) (snd p)`.
pub fn dep_uncurry_term(a : CoreTm, b : CoreTm, g_tm : CoreTm) -> CoreTm {
  let g_shifted = shift_core(g_tm, 1, 0)
  CLam(
    "p",
    CSigma("x", a, b),
    CApp(CApp(g_shifted, CFst(CVar(0))), CSnd(CVar(0))),
  )
}

///|
/// Theorem 3.3 (Dependent Skolem / Type-Theoretic Choice Isomorphism — Trotta et al. 2024):
/// Source Type: `Π(x:A). Σ(y:B(x)). C(x, y)` (where `C` is scoped over `Γ, x:A, y:B(x)`)
/// Target Type: `Σ(f : Π(x:A). B(x)). Π(x:A). C(x, f x)`
pub fn skolem_source_type(a : CoreTm, b : CoreTm, c_xy : CoreTm) -> CoreTm {
  CPi("x", a, CSigma("y", b, c_xy))
}

///|
pub fn skolem_target_type(a : CoreTm, b : CoreTm, c_xy : CoreTm) -> CoreTm {
  let fn_choice_ty = CPi("x", a, b)
  // Inside `f : Π(x:A).B(x), x : A[↑1]`:
  // Outer context vars shifted by +2; `f` is `#1`; `x` is `#0`; `y` becomes `(#1 #0)`!
  let a_under_f = shift_core(a, 1, 0)
  // `c_xy` has outer vars at `>= 2`, `x` at `1`, `y` at `0`:
  // First shift outer vars (`>= 2`) by +1 so outer vars sit above `f` (`#1`) and `x` (`#0` after subst):
  let c_outer_shifted = shift_core(c_xy, 1, 2)
  // Now in `c_outer_shifted` (before substituting `y` at 0), `x` is at 1, and after `subst0_core`,
  // `x` moves from 1 to 0, while `f` sits at 1! So substitute `y` (`#0`) with `(#1 #0)`:
  let c_fx = subst0_core(c_outer_shifted, CApp(CVar(1), CVar(0)))
  CSigma("f", fn_choice_ty, CPi("x", a_under_f, c_fx))
}

///|
/// Forward Skolemizer: `h : Πx:A. Σy:B(x). C(x, y)  ↦  < λx:A. fst(h x),  λx:A. snd(h x) >`.
pub fn skolemize_term(a : CoreTm, h_tm : CoreTm) -> CoreTm {
  let h1 = shift_core(h_tm, 1, 0)
  let witness_fn = CLam("x", a, CFst(CApp(h1, CVar(0))))
  let cert_fn = CLam("x", a, CSnd(CApp(h1, CVar(0))))
  CPair(witness_fn, cert_fn)
}

///|
/// Inverse Deskolemizer:
/// `s : Σ(f : Πx:A.B(x)). Πx:A. C(x, f x)  ↦  (λx:A. < (fst s) x, (snd s) x > : Πx:A. Σy:B(x). C(x, y))`.
/// Carries bidirectional annotation so `deskolemize_term` synthesizes its exact dependent codomain in head position!
pub fn deskolemize_term(
  a : CoreTm,
  b : CoreTm,
  c_xy : CoreTm,
  s_tm : CoreTm,
) -> CoreTm {
  let s1 = shift_core(s_tm, 1, 0)
  let raw_lam = CLam(
    "x",
    a,
    CPair(CApp(CFst(s1), CVar(0)), CApp(CSnd(s1), CVar(0))),
  )
  CAnn(raw_lam, skolem_source_type(a, b, c_xy))
}
