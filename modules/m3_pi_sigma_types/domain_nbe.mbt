///|
/// Module M3 — Core Syntax, Typed Kripke/Glued Semantic Domain, and Type-Directed
/// Normalization by Evaluation (NbE) for Π-Types, Σ-Types, Universes, Nat, Id, and Squash Prop.

///|
pub suberror TypeTheoryError {
  UnboundIndex(Int32, Int32)
  ExpectedTypeForm(String)
  ExpectedPiType(String)
  ExpectedSigmaType(String)
  ExpectedNatType
  ExpectedIdType
  ExpectedUnivCode(Int32)
  ConversionMismatch(CoreTm, CoreTm)
  UniverseCumulViolation(Int32, Int32)
  CannotSynthesizeUnannotated(String)
}

///|
#derive(Eq, Debug)
pub(all) enum CoreTm {
  CVar(Int32)
  CUniv(Int32)
  CProp
  CSmallEnc(Int32, CoreTm)
  CSmallDec(Int32, CoreTm)
  CPi(String, CoreTm, CoreTm)
  CLam(String, CoreTm, CoreTm)
  CApp(CoreTm, CoreTm)
  CSigma(String, CoreTm, CoreTm)
  CPair(CoreTm, CoreTm)
  CFst(CoreTm)
  CSnd(CoreTm)
  CUnit
  CStar
  CNat
  CZero
  CSucc(CoreTm)
  CNatRec(CoreTm, CoreTm, CoreTm, CoreTm)
  CId(CoreTm, CoreTm, CoreTm)
  CRefl(CoreTm)
  CJ(CoreTm, CoreTm, CoreTm, CoreTm, CoreTm, CoreTm)
  CSquash(CoreTm)
  CBoxProof(CoreTm)
  CAnn(CoreTm, CoreTm)
}

///|
pub extend CoreTm with Eq::{equal, not_equal}

///|
pub extend CoreTm with @debug.Debug::{to_repr}

///|
pub impl Show for CoreTm with fn output(self, logger) {
  match self {
    CVar(i) => logger.write_string("#\{i}")
    CUniv(l) => logger.write_string("U\{l}")
    CProp => logger.write_string("Prop")
    CSmallEnc(l, a) => {
      logger.write_string("Down\{l}(")
      Show::output(a, logger)
      logger.write_string(")")
    }
    CSmallDec(l, m) => {
      logger.write_string("Up\{l}(")
      Show::output(m, logger)
      logger.write_string(")")
    }
    CPi(x, a, b) => {
      logger.write_string("Pi(\{x}:")
      Show::output(a, logger)
      logger.write_string(").")
      Show::output(b, logger)
    }
    CLam(x, a, b) => {
      logger.write_string("lam(\{x}:")
      Show::output(a, logger)
      logger.write_string(").")
      Show::output(b, logger)
    }
    CApp(f, a) => {
      logger.write_string("(")
      Show::output(f, logger)
      logger.write_string(" ")
      Show::output(a, logger)
      logger.write_string(")")
    }
    CSigma(x, a, b) => {
      logger.write_string("Sigma(\{x}:")
      Show::output(a, logger)
      logger.write_string(").")
      Show::output(b, logger)
    }
    CPair(a, b) => {
      logger.write_string("<")
      Show::output(a, logger)
      logger.write_string(", ")
      Show::output(b, logger)
      logger.write_string(">")
    }
    CFst(p) => {
      logger.write_string("fst(")
      Show::output(p, logger)
      logger.write_string(")")
    }
    CSnd(p) => {
      logger.write_string("snd(")
      Show::output(p, logger)
      logger.write_string(")")
    }
    CUnit => logger.write_string("Unit")
    CStar => logger.write_string("tt")
    CNat => logger.write_string("Nat")
    CZero => logger.write_string("0")
    CSucc(n) => {
      logger.write_string("S(")
      Show::output(n, logger)
      logger.write_string(")")
    }
    CNatRec(_, z, s, n) => {
      logger.write_string("natrec(")
      Show::output(z, logger)
      logger.write_string(", ")
      Show::output(s, logger)
      logger.write_string(", ")
      Show::output(n, logger)
      logger.write_string(")")
    }
    CId(t, l, r) => {
      logger.write_string("Id(")
      Show::output(t, logger)
      logger.write_string(", ")
      Show::output(l, logger)
      logger.write_string(", ")
      Show::output(r, logger)
      logger.write_string(")")
    }
    CRefl(x) => {
      logger.write_string("refl(")
      Show::output(x, logger)
      logger.write_string(")")
    }
    CJ(_, _, _, rf, _, p) => {
      logger.write_string("J(")
      Show::output(rf, logger)
      logger.write_string(", ")
      Show::output(p, logger)
      logger.write_string(")")
    }
    CSquash(a) => {
      logger.write_string("||")
      Show::output(a, logger)
      logger.write_string("||")
    }
    CBoxProof(p) => {
      logger.write_string("|")
      Show::output(p, logger)
      logger.write_string("|")
    }
    CAnn(e, t) => {
      logger.write_string("(")
      Show::output(e, logger)
      logger.write_string(" : ")
      Show::output(t, logger)
      logger.write_string(")")
    }
  }
}

///|
pub extend CoreTm with Show::{to_string, output}

///|
/// Shift De Bruijn indices >= `cutoff` in `CoreTm` by `delta`.
pub fn shift_core(tm : CoreTm, delta : Int32, cutoff : Int32) -> CoreTm {
  if delta == 0 {
    return tm
  }
  match tm {
    CVar(i) => if i >= cutoff { CVar(i + delta) } else { tm }
    CUniv(_) | CProp | CUnit | CStar | CNat | CZero => tm
    CSmallEnc(l, a) => CSmallEnc(l, shift_core(a, delta, cutoff))
    CSmallDec(l, m) => CSmallDec(l, shift_core(m, delta, cutoff))
    CPi(x, a, b) =>
      CPi(x, shift_core(a, delta, cutoff), shift_core(b, delta, cutoff + 1))
    CLam(x, a, b) =>
      CLam(x, shift_core(a, delta, cutoff), shift_core(b, delta, cutoff + 1))
    CApp(f, a) =>
      CApp(shift_core(f, delta, cutoff), shift_core(a, delta, cutoff))
    CSigma(x, a, b) =>
      CSigma(x, shift_core(a, delta, cutoff), shift_core(b, delta, cutoff + 1))
    CPair(a, b) =>
      CPair(shift_core(a, delta, cutoff), shift_core(b, delta, cutoff))
    CFst(p) => CFst(shift_core(p, delta, cutoff))
    CSnd(p) => CSnd(shift_core(p, delta, cutoff))
    CSucc(n) => CSucc(shift_core(n, delta, cutoff))
    CNatRec(m, z, s, n) =>
      CNatRec(
        shift_core(m, delta, cutoff + 1),
        shift_core(z, delta, cutoff),
        shift_core(s, delta, cutoff + 2),
        shift_core(n, delta, cutoff),
      )
    CId(t, l, r) =>
      CId(
        shift_core(t, delta, cutoff),
        shift_core(l, delta, cutoff),
        shift_core(r, delta, cutoff),
      )
    CRefl(x) => CRefl(shift_core(x, delta, cutoff))
    CJ(t, l, m, rf, r, p) =>
      CJ(
        shift_core(t, delta, cutoff),
        shift_core(l, delta, cutoff),
        shift_core(m, delta, cutoff + 2),
        shift_core(rf, delta, cutoff),
        shift_core(r, delta, cutoff),
        shift_core(p, delta, cutoff),
      )
    CSquash(a) => CSquash(shift_core(a, delta, cutoff))
    CBoxProof(a) => CBoxProof(shift_core(a, delta, cutoff))
    CAnn(e, t) =>
      CAnn(shift_core(e, delta, cutoff), shift_core(t, delta, cutoff))
  }
}

///|
/// Defunctionalized Semantic Closure over De Bruijn-Level Environment `env`
#derive(Debug)
pub(all) struct Clos {
  env : Array[Val]
  body : CoreTm
}

///|
pub extend Clos with @debug.Debug::{to_repr}

///|
#derive(Debug)
pub(all) enum SpineElim {
  SEApp(Val, Val)
  SEFst
  SESnd
  SESmallDec(Int32)
  SENatRec(Clos, Val, Clos)
  SEJ(Val, Val, Clos, Val, Val)
}

///|
pub extend SpineElim with @debug.Debug::{to_repr}

///|
#derive(Debug)
pub(all) struct Neutral {
  head_lvl : Int32
  spine : Array[SpineElim]
}

///|
pub extend Neutral with @debug.Debug::{to_repr}

///|
#derive(Debug)
pub(all) enum Val {
  VNeu(Val, Neutral)
  VUniv(Int32)
  VProp
  VSmallEnc(Int32, Val)
  VPi(String, Val, Clos)
  VLam(String, Val, Clos)
  VSigma(String, Val, Clos)
  VPair(Val, Val)
  VUnit
  VStar
  VNat
  VZero
  VSucc(Val)
  VId(Val, Val, Val)
  VRefl(Val)
  VSquash(Val)
  VBoxProof(Val)
}

///|
pub extend Val with @debug.Debug::{to_repr}

///|
/// Construct a fresh semantic variable at De Bruijn level `lvl` of semantic type `vty`.
pub fn fresh_neutral_var(lvl : Int32, vty : Val) -> Val {
  VNeu(vty, { head_lvl: lvl, spine: [], })
}

///|
/// Instantiate single-binder closure `clos` with semantic argument `arg`.
pub fn eval_clos(clos : Clos, arg : Val) -> Val {
  let next_env = clos.env.copy()
  next_env.push(arg)
  eval_tm(next_env, clos.body)
}

///|
/// Instantiate two-binder closure `clos` (e.g. NatRec step or J motive) with `(arg1, arg2)`.
pub fn eval_clos2(clos : Clos, arg1 : Val, arg2 : Val) -> Val {
  let next_env = clos.env.copy()
  next_env.push(arg1)
  next_env.push(arg2)
  eval_tm(next_env, clos.body)
}

///|
/// Local Axiom (Logical Elimination for Π): Semantic Application `f(arg)`.
pub fn apply_val(fn_val : Val, arg : Val) -> Val {
  match fn_val {
    VLam(_, _, clos) => eval_clos(clos, arg)
    VNeu(VPi(_, dom, cod_clos), ne) => {
      let res_ty = eval_clos(cod_clos, arg)
      let next_spine = ne.spine.copy()
      next_spine.push(SEApp(dom, arg))
      VNeu(res_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    VNeu(other_ty, ne) => {
      let next_spine = ne.spine.copy()
      next_spine.push(SEApp(VUnit, arg))
      VNeu(other_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    _ => fn_val
  }
}

///|
/// Local Axiom (Logical Elimination β_1 for Σ): First Projection `fst(p)`.
pub fn fst_val(p : Val) -> Val {
  match p {
    VPair(a, _) => a
    VNeu(VSigma(_, fst_ty, _), ne) => {
      let next_spine = ne.spine.copy()
      next_spine.push(SEFst)
      VNeu(fst_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    VNeu(other_ty, ne) => {
      let next_spine = ne.spine.copy()
      next_spine.push(SEFst)
      VNeu(other_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    _ => p
  }
}

///|
/// Local Axiom (Logical Elimination β_2 for Σ): Dependent Second Projection `snd(p)`.
pub fn snd_val(p : Val) -> Val {
  match p {
    VPair(_, b) => b
    VNeu(VSigma(_, _, snd_clos), ne) => {
      let p1 = fst_val(p)
      let snd_ty = eval_clos(snd_clos, p1)
      let next_spine = ne.spine.copy()
      next_spine.push(SESnd)
      VNeu(snd_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    VNeu(other_ty, ne) => {
      let next_spine = ne.spine.copy()
      next_spine.push(SESnd)
      VNeu(other_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    _ => p
  }
}

///|
/// Local Axiom (`univ-beta` for Sterbac-Sterling Fuss-Free Universes): `⇑_i (⇓_j A) -> A`.
pub fn small_dec_val(lvl : Int32, code : Val) -> Val {
  match code {
    VSmallEnc(_, inner_ty) => inner_ty
    VNeu(_, ne) => {
      let next_spine = ne.spine.copy()
      next_spine.push(SESmallDec(lvl))
      VNeu(VUniv(lvl), { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    _ => code
  }
}

///|
/// Local Axiom (ι-Elimination for Nat): Dependent Primitive Recursion `natrec`.
pub fn natrec_val(motive : Clos, base : Val, step : Clos, target : Val) -> Val {
  match target {
    VZero => base
    VSucc(pred) => {
      let ih = natrec_val(motive, base, step, pred)
      eval_clos2(step, pred, ih)
    }
    VNeu(_, ne) => {
      let res_ty = eval_clos(motive, target)
      let next_spine = ne.spine.copy()
      next_spine.push(SENatRec(motive, base, step))
      VNeu(res_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    _ => base
  }
}

///|
/// Local Axiom (ι-Elimination for Identity Type): Martin-Löf `J` Eliminator.
pub fn j_elim_val(
  ty : Val,
  lhs : Val,
  motive : Clos,
  refl_case : Val,
  rhs : Val,
  eq_proof : Val,
) -> Val {
  match eq_proof {
    VRefl(_) => refl_case
    VNeu(_, ne) => {
      let res_ty = eval_clos2(motive, rhs, eq_proof)
      let next_spine = ne.spine.copy()
      next_spine.push(SEJ(ty, lhs, motive, refl_case, rhs))
      VNeu(res_ty, { head_lvl: ne.head_lvl, spine: next_spine, })
    }
    _ => refl_case
  }
}

///|
/// Evaluate syntax `CoreTm` (with De Bruijn indices) in environment `env` (indexed by De Bruijn levels!).
/// Mirror lookup: `Var(i)` resolves to `env[env.length() - 1 - i]` in O(1)!
pub fn eval_tm(env : Array[Val], tm : CoreTm) -> Val {
  match tm {
    CVar(idx) => {
      let pos = env.length() - 1 - idx
      if pos >= 0 && pos < env.length() {
        env[pos]
      } else {
        fresh_neutral_var(0, VUnit)
      }
    }
    CUniv(l) => VUniv(l)
    CProp => VProp
    CSmallEnc(l, a) => {
      let va = eval_tm(env, a)
      match va {
        // `univ-ext` / `univ-eta`: Down_l(Up_l(m)) == m when levels match
        VNeu(VUniv(src_l), { head_lvl, spine, }) =>
          if spine.length() > 0 {
            match spine[spine.length() - 1] {
              SESmallDec(dec_l) =>
                if dec_l == l {
                  let trimmed : Array[SpineElim] = []
                  for k = 0; k < spine.length() - 1; k = k + 1 {
                    trimmed.push(spine[k])
                  }
                  return VNeu(VUniv(src_l), { head_lvl, spine: trimmed, })
                }
              _ => ()
            }
          }
        _ => ()
      }
      VSmallEnc(l, va)
    }
    CSmallDec(l, m) => small_dec_val(l, eval_tm(env, m))
    CPi(x, dom, cod) =>
      VPi(x, eval_tm(env, dom), { env: env.copy(), body: cod, })
    CLam(x, dom, body) => VLam(x, eval_tm(env, dom), { env: env.copy(), body, })
    CApp(f, a) => apply_val(eval_tm(env, f), eval_tm(env, a))
    CSigma(x, fst_t, snd_t) =>
      VSigma(x, eval_tm(env, fst_t), { env: env.copy(), body: snd_t, })
    CPair(a, b) => VPair(eval_tm(env, a), eval_tm(env, b))
    CFst(p) => fst_val(eval_tm(env, p))
    CSnd(p) => snd_val(eval_tm(env, p))
    CUnit => VUnit
    CStar => VStar
    CNat => VNat
    CZero => VZero
    CSucc(n) => VSucc(eval_tm(env, n))
    CNatRec(motive, base, step, target) =>
      natrec_val(
        { env: env.copy(), body: motive, },
        eval_tm(env, base),
        { env: env.copy(), body: step, },
        eval_tm(env, target),
      )
    CId(t, l, r) => VId(eval_tm(env, t), eval_tm(env, l), eval_tm(env, r))
    CRefl(x) => VRefl(eval_tm(env, x))
    CJ(t, l, m, rf, r, p) =>
      j_elim_val(
        eval_tm(env, t),
        eval_tm(env, l),
        { env: env.copy(), body: m, },
        eval_tm(env, rf),
        eval_tm(env, r),
        eval_tm(env, p),
      )
    CSquash(a) => VSquash(eval_tm(env, a))
    CBoxProof(p) => VBoxProof(eval_tm(env, p))
    CAnn(e, _) => eval_tm(env, e)
  }
}

///|
/// Type-Directed Readback of Semantic Type `vty` at binder depth `depth` into βη-Canonical `CoreTm`.
pub fn quote_ty(depth : Int32, vty : Val) -> CoreTm {
  match vty {
    VUniv(l) => CUniv(l)
    VProp => CProp
    VUnit => CUnit
    VNat => CNat
    VPi(x, dom, cod_clos) => {
      let q_dom = quote_ty(depth, dom)
      let v_var = fresh_neutral_var(depth, dom)
      let q_cod = quote_ty(depth + 1, eval_clos(cod_clos, v_var))
      CPi(x, q_dom, q_cod)
    }
    VSigma(x, fst_t, snd_clos) => {
      let q_fst = quote_ty(depth, fst_t)
      let v_var = fresh_neutral_var(depth, fst_t)
      let q_snd = quote_ty(depth + 1, eval_clos(snd_clos, v_var))
      CSigma(x, q_fst, q_snd)
    }
    VId(t, l, r) =>
      CId(quote_ty(depth, t), quote_val(depth, t, l), quote_val(depth, t, r))
    VSquash(a) => CSquash(quote_ty(depth, a))
    VNeu(_, ne) => quote_neutral(depth, ne)
    other => quote_untyped(depth, other)
  }
}

///|
/// Type-Directed Readback of Semantic Value `v` at type `vty` and depth `depth`:
/// Enforces full η-laws for Π-types, Σ-types, Unit, and canonical Squash proof-irrelevance!
pub fn quote_val(depth : Int32, vty : Val, v : Val) -> CoreTm {
  match vty {
    // Unit η-law: every inhabitant of Unit is definitionally `tt` (`CStar`) in O(1)!
    VUnit => CStar
    // Squash Prop Proof Irrelevance: every proof of ||A|| quotes canonically to `|tt|`!
    VSquash(_) => CBoxProof(CStar)
    // Π η-law: read back `f` at `Pi(x:A).B` as `lam(x:A). quote(f(#depth))`
    VPi(x, dom, cod_clos) => {
      let q_dom = quote_ty(depth, dom)
      let arg_var = fresh_neutral_var(depth, dom)
      let body_val = apply_val(v, arg_var)
      let body_ty = eval_clos(cod_clos, arg_var)
      CLam(x, q_dom, quote_val(depth + 1, body_ty, body_val))
    }
    // Σ η-law (Surjective Pairing): read back `p` at `Sigma(x:A).B` as `<fst(p), snd(p)>`
    VSigma(_, fst_t, snd_clos) => {
      let p1 = fst_val(v)
      let p2 = snd_val(v)
      let snd_t = eval_clos(snd_clos, p1)
      CPair(quote_val(depth, fst_t, p1), quote_val(depth, snd_t, p2))
    }
    VUniv(l) =>
      match v {
        VSmallEnc(_, inner_ty) => CSmallEnc(l, quote_ty(depth, inner_ty))
        VNeu(_, ne) => quote_neutral(depth, ne)
        _ => quote_ty(depth, v)
      }
    _ => quote_untyped(depth, v)
  }
}

///|
fn quote_untyped(depth : Int32, v : Val) -> CoreTm {
  match v {
    VNeu(_, ne) => quote_neutral(depth, ne)
    VUniv(l) => CUniv(l)
    VProp => CProp
    VSmallEnc(l, inner) => CSmallEnc(l, quote_ty(depth, inner))
    VPi(_, _, _) | VSigma(_, _, _) | VId(_, _, _) | VSquash(_) =>
      quote_ty(depth, v)
    VLam(x, dom, clos) => {
      let q_dom = quote_ty(depth, dom)
      let v_var = fresh_neutral_var(depth, dom)
      CLam(x, q_dom, quote_untyped(depth + 1, eval_clos(clos, v_var)))
    }
    VPair(a, b) => CPair(quote_untyped(depth, a), quote_untyped(depth, b))
    VUnit => CUnit
    VStar => CStar
    VNat => CNat
    VZero => CZero
    VSucc(n) => CSucc(quote_untyped(depth, n))
    VRefl(x) => CRefl(quote_untyped(depth, x))
    VBoxProof(_) => CBoxProof(CStar)
  }
}

///|
fn quote_neutral(depth : Int32, ne : Neutral) -> CoreTm {
  let idx = depth - 1 - ne.head_lvl
  let mut acc = CVar(if idx >= 0 { idx } else { 0 })
  for elim in ne.spine {
    match elim {
      SEApp(arg_ty, arg_val) =>
        acc = CApp(acc, quote_val(depth, arg_ty, arg_val))
      SEFst => acc = CFst(acc)
      SESnd => acc = CSnd(acc)
      SESmallDec(l) => acc = CSmallDec(l, acc)
      SENatRec(mot, base, step) => {
        let n_var = fresh_neutral_var(depth, VNat)
        let q_mot = quote_ty(depth + 1, eval_clos(mot, n_var))
        let z_ty = eval_clos(mot, VZero)
        let q_base = quote_val(depth, z_ty, base)
        let k_var = fresh_neutral_var(depth, VNat)
        let ih_ty = eval_clos(mot, k_var)
        let ih_var = fresh_neutral_var(depth + 1, ih_ty)
        let step_ty = eval_clos(mot, VSucc(k_var))
        let q_step = quote_val(
          depth + 2,
          step_ty,
          eval_clos2(step, k_var, ih_var),
        )
        acc = CNatRec(q_mot, q_base, q_step, acc)
      }
      SEJ(ty, lhs, mot, rf, rhs) => {
        let q_ty = quote_ty(depth, ty)
        let q_lhs = quote_val(depth, ty, lhs)
        let y_var = fresh_neutral_var(depth, ty)
        let p_var = fresh_neutral_var(depth + 1, VId(ty, lhs, y_var))
        let q_mot = quote_ty(depth + 2, eval_clos2(mot, y_var, p_var))
        let rf_ty = eval_clos2(mot, lhs, VRefl(lhs))
        let q_rf = quote_val(depth, rf_ty, rf)
        let q_rhs = quote_val(depth, ty, rhs)
        acc = CJ(q_ty, q_lhs, q_mot, q_rf, q_rhs, acc)
      }
    }
  }
  acc
}

///|
/// Decide judgmental type equality `Γ ⊢ A ≡ B type` via NbE canonical quotation!
pub fn conv_ty(depth : Int32, a : Val, b : Val) -> Bool {
  quote_ty(depth, a) == quote_ty(depth, b)
}

///|
/// Decide judgmental term equality `Γ ⊢ u ≡ v : A` via Type-Directed NbE (including η & Proof Irrelevance)!
pub fn conv_val(depth : Int32, vty : Val, u : Val, v : Val) -> Bool {
  match vty {
    VUnit | VSquash(_) => true
    _ => quote_val(depth, vty, u) == quote_val(depth, vty, v)
  }
}

///|
/// Decode closed canonical numeral `CoreTm` into `Int32`, raising `ExpectedNatType` if non-canonical.
pub fn decode_nat_numeral(tm : CoreTm) -> Int32 raise TypeTheoryError {
  match tm {
    CZero => 0
    CSucc(pred) => 1 + decode_nat_numeral(pred)
    _ => raise TypeTheoryError::ExpectedNatType
  }
}

///|
/// Encode non-negative `Int32` into canonical `CoreTm` numeral `S^n(0)`.
pub fn encode_nat_numeral(n : Int32) -> CoreTm {
  let mut acc = CZero
  for i = 0; i < n; i = i + 1 {
    let _ = i
    acc = CSucc(acc)
  }
  acc
}
