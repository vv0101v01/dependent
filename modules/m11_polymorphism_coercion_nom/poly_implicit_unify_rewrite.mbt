///|
/// Module M11 (Part 1):
/// 1. Dependent Polymorphism (`DepPolyScheme`) & Binary Relational Parametricity Synthesis
/// 2. Implicit Argument Elaboration (`{x : A} -> B` -> `?m[spine]`)
/// 3. Miller Higher-Order Pattern Unification with Spine Pruning & Occurs Check
/// 4. Weight-Guarded Terminating Implicit Term Rewriting (`lhs ~> rhs`).

///|
pub(all) suberror PolyElabError {
  NonLinearMetaSpine(Int32)
  MetaOccursCheckFailed(Int32)
  MetaScopeEscape(Int32, Int32)
  UnificationSymbolClash(ElabTm, ElabTm)
  NonDecreasingRewriteRule(String)
  UnboundRewritePatternVar(Int32)
  UniversePolymorphismArityMismatch(Int32, Int32)
  IncoherentCoercionDiamond(String, String)
  DuplicateRecordField(Int32)
  MissingStructuralField(Int32)
  NominalBrandMismatch(Int32, Int32)
  CoercionUnavailable
}

///|
#derive(Eq, Debug)
pub(all) enum ElabTm {
  EVar(Int32)
  EPatVar(Int32)
  EMeta(Int32, Array[Int32])
  EUniv(Int32)
  EPolyUniv(Int32)
  EBase(String)
  EPi(Bool, String, ElabTm, ElabTm)
  ELam(Bool, String, ElabTm, ElabTm)
  EApp(Bool, ElabTm, ElabTm)
  ESym(String, Array[ElabTm])
}

///|
pub extend ElabTm with Eq::{equal, not_equal}

///|
pub extend ElabTm with @debug.Debug::{to_repr}

///|
/// Dependent Polymorphic Type Scheme:
/// Quantifies over `univ_arity` algebraic universe parameters + `implicit_tele` dependent implicit binders `{x_i : T_i}`!
#derive(Eq, Debug)
pub(all) struct DepPolyScheme {
  name : String
  univ_arity : Int32
  implicit_tele : Array[(String, ElabTm)]
  body_ty : ElabTm
}

///|
pub extend DepPolyScheme with Eq::{equal, not_equal}

///|
pub extend DepPolyScheme with @debug.Debug::{to_repr}

///|
pub fn subst_poly_univs(
  tm : ElabTm,
  levels : Array[Int32],
) -> ElabTm raise PolyElabError {
  match tm {
    EPolyUniv(i) => {
      if i < 0 || i >= levels.length() {
        raise PolyElabError::UniversePolymorphismArityMismatch(
          i,
          levels.length(),
        )
      }
      EUniv(levels[i])
    }
    EVar(_) | EPatVar(_) | EMeta(_, _) | EUniv(_) | EBase(_) => tm
    EPi(imp, x, a, b) =>
      EPi(imp, x, subst_poly_univs(a, levels), subst_poly_univs(b, levels))
    ELam(imp, x, a, b) =>
      ELam(imp, x, subst_poly_univs(a, levels), subst_poly_univs(b, levels))
    EApp(imp, f, a) =>
      EApp(imp, subst_poly_univs(f, levels), subst_poly_univs(a, levels))
    ESym(s, args) => {
      let out : Array[ElabTm] = []
      for x in args {
        out.push(subst_poly_univs(x, levels))
      }
      ESym(s, out)
    }
  }
}

///|
pub fn shift_elab(tm : ElabTm, delta : Int32, cutoff : Int32) -> ElabTm {
  if delta == 0 {
    return tm
  }
  match tm {
    EVar(i) => if i >= cutoff { EVar(i + delta) } else { tm }
    EPatVar(_) | EUniv(_) | EPolyUniv(_) | EBase(_) => tm
    EMeta(m, spine) => {
      let ns : Array[Int32] = []
      for v in spine {
        ns.push(if v >= cutoff { v + delta } else { v })
      }
      EMeta(m, ns)
    }
    EPi(imp, x, a, b) =>
      EPi(
        imp,
        x,
        shift_elab(a, delta, cutoff),
        shift_elab(b, delta, cutoff + 1),
      )
    ELam(imp, x, a, b) =>
      ELam(
        imp,
        x,
        shift_elab(a, delta, cutoff),
        shift_elab(b, delta, cutoff + 1),
      )
    EApp(imp, f, a) =>
      EApp(imp, shift_elab(f, delta, cutoff), shift_elab(a, delta, cutoff))
    ESym(s, args) => {
      let out : Array[ElabTm] = []
      for x in args {
        out.push(shift_elab(x, delta, cutoff))
      }
      ESym(s, out)
    }
  }
}

///|
pub fn subst_elab(tm : ElabTm, target : Int32, repl : ElabTm) -> ElabTm {
  match tm {
    EVar(i) =>
      if i == target {
        repl
      } else if i > target {
        EVar(i - 1)
      } else {
        tm
      }
    EPatVar(_) | EUniv(_) | EPolyUniv(_) | EBase(_) => tm
    EMeta(m, spine) => {
      // If spine only contains variables != target, adjust indices; otherwise instantiate via explicit beta!
      let mut hits_target = false
      for v in spine {
        if v == target {
          hits_target = true
        }
      }
      if !hits_target {
        let ns : Array[Int32] = []
        for v in spine {
          ns.push(if v > target { v - 1 } else { v })
        }
        EMeta(m, ns)
      } else {
        EMeta(m, spine)
      }
    }
    EPi(imp, x, a, b) =>
      EPi(
        imp,
        x,
        subst_elab(a, target, repl),
        subst_elab(b, target + 1, shift_elab(repl, 1, 0)),
      )
    ELam(imp, x, a, b) =>
      ELam(
        imp,
        x,
        subst_elab(a, target, repl),
        subst_elab(b, target + 1, shift_elab(repl, 1, 0)),
      )
    EApp(imp, f, a) =>
      EApp(imp, subst_elab(f, target, repl), subst_elab(a, target, repl))
    ESym(s, args) => {
      let out : Array[ElabTm] = []
      for x in args {
        out.push(subst_elab(x, target, repl))
      }
      ESym(s, out)
    }
  }
}

///|
/// Contextual Metavariable Store for Implicit Argument Elaboration & Miller Pattern Unification!
/// Each solved metavariable `?m` stores `(spine_arity, body)` representing a closed `spine_arity`-arg function!
pub struct MetaStore {
  mut next_meta : Int32
  solutions : Map[Int32, (Int32, ElabTm)]
}

///|
pub fn MetaStore::new() -> MetaStore {
  { next_meta: 0, solutions: Map([]), }
}

///|
pub fn MetaStore::fresh_meta(
  self : MetaStore,
  ctx_depth : Int32,
) -> (Int32, ElabTm) {
  let id = self.next_meta
  self.next_meta = id + 1
  let spine : Array[Int32] = []
  for i = 0; i < ctx_depth; i = i + 1 {
    spine.push(ctx_depth - 1 - i)
  }
  (id, EMeta(id, spine))
}

///|
/// Elaborate an application of a Dependent Polymorphic Scheme `scheme` at concrete universe `levels`
/// in context of depth `ctx_depth`:
/// Automatically instantiates universe variables AND inserts fresh contextual metavariables `?m_i`
/// for every implicit `{x_i : T_i}` binder, returning `(applied_term, elaborated_body_type, meta_ids)`!
pub fn instantiate_poly_scheme_implicits(
  store : MetaStore,
  head_tm : ElabTm,
  scheme : DepPolyScheme,
  levels : Array[Int32],
  ctx_depth : Int32,
) -> (ElabTm, ElabTm, Array[Int32]) raise PolyElabError {
  if levels.length() != scheme.univ_arity {
    raise PolyElabError::UniversePolymorphismArityMismatch(
      levels.length(),
      scheme.univ_arity,
    )
  }
  let mut cur_tm = head_tm
  let mut cur_ty = subst_poly_univs(scheme.body_ty, levels)
  let metas : Array[Int32] = []
  let k = scheme.implicit_tele.length()
  // Note: `body_ty` is scoped under `k` implicit binders (`#k-1` outermost .. `#0` innermost).
  // Substitute outermost-first: create `k` metavariables `[m_0, ..., m_{k-1}]`, then substitute!
  let meta_tms : Array[ElabTm] = []
  for i = 0; i < k; i = i + 1 {
    let (mid, mtm) = store.fresh_meta(ctx_depth)
    metas.push(mid)
    meta_tms.push(mtm)
    cur_tm = EApp(true, cur_tm, mtm)
  }
  // Substitute `#(k - 1 - i)` from `i = 0` down to `k - 1`:
  for i = 0; i < k; i = i + 1 {
    let target = k - 1 - i
    cur_ty = subst_elab(cur_ty, target, shift_elab(meta_tms[i], target, 0))
  }
  (cur_tm, cur_ty, metas)
}

///|
/// Bernardy-Reynolds Binary Relational Parametricity Descriptor:
/// Given a polymorphic scheme with `n_type_params` type parameters and `n_val_args` value arguments,
/// computes total relational abstraction arity `3 * n_type_params + 3 * n_val_args`
/// (`(A1, A2, A_R)` per type parameter and `(x1, x2, x_R)` per value argument)!
pub fn relational_parametricity_arity(
  n_type_params : Int32,
  n_val_args : Int32,
) -> Int32 {
  3 * n_type_params + 3 * n_val_args
}

///|
/// Zonk (substitute all solved metavariables recursively) inside `ElabTm`!
pub fn MetaStore::zonk(self : MetaStore, tm : ElabTm) -> ElabTm {
  match tm {
    EVar(_) | EPatVar(_) | EUniv(_) | EPolyUniv(_) | EBase(_) => tm
    EMeta(m, spine) =>
      match self.solutions.get(m) {
        None => tm
        Some((arity, sol_body)) => {
          // `sol_body` has `arity` bound variables where `#(arity - 1 - j)` corresponds to `spine[j]`!
          let mut inst = sol_body
          for j = 0; j < arity; j = j + 1 {
            let target = arity - 1 - j
            inst = subst_elab(inst, target, EVar(spine[j] + target))
          }
          self.zonk(inst)
        }
      }
    EPi(imp, x, a, b) => EPi(imp, x, self.zonk(a), self.zonk(b))
    ELam(imp, x, a, b) => ELam(imp, x, self.zonk(a), self.zonk(b))
    EApp(imp, f, a) => EApp(imp, self.zonk(f), self.zonk(a))
    ESym(s, args) => {
      let out : Array[ElabTm] = []
      for x in args {
        out.push(self.zonk(x))
      }
      ESym(s, out)
    }
  }
}

///|
/// Weight-Guarded Terminating Implicit Term Rewrite Rule `lhs ~> rhs`
/// (uses `EPatVar(p)` for rewrite pattern variables!).
#derive(Eq, Debug)
pub(all) struct ImplicitRewriteRule {
  name : String
  lhs : ElabTm
  rhs : ElabTm
}

///|
pub extend ImplicitRewriteRule with Eq::{equal, not_equal}

///|
pub extend ImplicitRewriteRule with @debug.Debug::{to_repr}

///|
fn knuth_bendix_weight(tm : ElabTm, pat_vars : Map[Int32, Int32]) -> Int32 {
  match tm {
    EPatVar(p) => {
      let prev = match pat_vars.get(p) {
        Some(c) => c
        None => 0
      }
      pat_vars[p] = prev + 1
      1
    }
    EVar(_) | EMeta(_, _) | EUniv(_) | EPolyUniv(_) | EBase(_) => 1
    EPi(_, _, a, b) | ELam(_, _, a, b) | EApp(_, a, b) =>
      2 + knuth_bendix_weight(a, pat_vars) + knuth_bendix_weight(b, pat_vars)
    ESym(_, args) => {
      let mut w = 2
      for x in args {
        w = w + knuth_bendix_weight(x, pat_vars)
      }
      w
    }
  }
}

///|
/// Verify Knuth-Bendix Decreasing Weight & Non-Duplicating Variable Condition (`lhs ~> rhs`),
/// guaranteeing polynomial-time strong termination of implicit index rewriting!
pub fn verify_rewrite_rule_terminating(
  rule : ImplicitRewriteRule,
) -> Bool raise PolyElabError {
  let lhs_vars : Map[Int32, Int32] = Map([])
  let rhs_vars : Map[Int32, Int32] = Map([])
  let wl = knuth_bendix_weight(rule.lhs, lhs_vars)
  let wr = knuth_bendix_weight(rule.rhs, rhs_vars)
  if wl <= wr {
    raise PolyElabError::NonDecreasingRewriteRule(rule.name)
  }
  for kv in rhs_vars {
    let p = kv.0
    let r_cnt = kv.1
    match lhs_vars.get(p) {
      None => raise PolyElabError::UnboundRewritePatternVar(p)
      Some(l_cnt) =>
        if r_cnt > l_cnt {
          raise PolyElabError::NonDecreasingRewriteRule(rule.name)
        }
    }
  }
  true
}

///|
fn match_rewrite_pat(
  pat : ElabTm,
  scrut : ElabTm,
  bindings : Map[Int32, ElabTm],
) -> Bool {
  match pat {
    EPatVar(p) =>
      match bindings.get(p) {
        None => {
          bindings[p] = scrut
          true
        }
        Some(prev) => prev == scrut
      }
    ESym(s1, a1) =>
      match scrut {
        ESym(s2, a2) => {
          if s1 != s2 || a1.length() != a2.length() {
            return false
          }
          for i = 0; i < a1.length(); i = i + 1 {
            if !match_rewrite_pat(a1[i], a2[i], bindings) {
              return false
            }
          }
          true
        }
        _ => false
      }
    _ => pat == scrut
  }
}

///|
fn inst_rewrite_rhs(rhs : ElabTm, bindings : Map[Int32, ElabTm]) -> ElabTm {
  match rhs {
    EPatVar(p) =>
      match bindings.get(p) {
        Some(v) => v
        None => rhs
      }
    ESym(s, args) => {
      let out : Array[ElabTm] = []
      for x in args {
        out.push(inst_rewrite_rhs(x, bindings))
      }
      ESym(s, out)
    }
    EPi(imp, x, a, b) =>
      EPi(imp, x, inst_rewrite_rhs(a, bindings), inst_rewrite_rhs(b, bindings))
    ELam(imp, x, a, b) =>
      ELam(imp, x, inst_rewrite_rhs(a, bindings), inst_rewrite_rhs(b, bindings))
    EApp(imp, f, a) =>
      EApp(imp, inst_rewrite_rhs(f, bindings), inst_rewrite_rhs(a, bindings))
    _ => rhs
  }
}

///|
/// Bottom-Up Terminating Implicit Term Rewriter!
pub fn rewrite_normalize(
  rules : Array[ImplicitRewriteRule],
  tm : ElabTm,
) -> ElabTm {
  let step_children = match tm {
    ESym(s, args) => {
      let na : Array[ElabTm] = []
      for x in args {
        na.push(rewrite_normalize(rules, x))
      }
      ESym(s, na)
    }
    EPi(imp, x, a, b) =>
      EPi(imp, x, rewrite_normalize(rules, a), rewrite_normalize(rules, b))
    ELam(imp, x, a, b) =>
      ELam(imp, x, rewrite_normalize(rules, a), rewrite_normalize(rules, b))
    EApp(imp, f, a) =>
      EApp(imp, rewrite_normalize(rules, f), rewrite_normalize(rules, a))
    _ => tm
  }
  for r in rules {
    let b : Map[Int32, ElabTm] = Map([])
    if match_rewrite_pat(r.lhs, step_children, b) {
      return rewrite_normalize(rules, inst_rewrite_rhs(r.rhs, b))
    }
  }
  step_children
}

///|
fn occurs_in(meta_id : Int32, tm : ElabTm) -> Bool {
  match tm {
    EMeta(m, _) => m == meta_id
    EPi(_, _, a, b) | ELam(_, _, a, b) | EApp(_, a, b) =>
      occurs_in(meta_id, a) || occurs_in(meta_id, b)
    ESym(_, args) => {
      for x in args {
        if occurs_in(meta_id, x) {
          return true
        }
      }
      false
    }
    _ => false
  }
}

///|
/// Invert `rhs` under Miller Pattern Spine `spine = [v_0, ..., v_{k-1}]` (`binder_offset` tracks inner lambdas):
/// Maps `EVar(v_j + binder_offset)` to `EVar(k - 1 - j + binder_offset)` and raises `MetaScopeEscape` if
/// any outer free variable not in `spine` occurs!
fn miller_invert(
  meta_id : Int32,
  spine : Array[Int32],
  tm : ElabTm,
  binder_offset : Int32,
) -> ElabTm raise PolyElabError {
  let k = spine.length()
  match tm {
    EVar(idx) => {
      if idx < binder_offset {
        return EVar(idx)
      }
      let outer_idx = idx - binder_offset
      for j = 0; j < k; j = j + 1 {
        if spine[j] == outer_idx {
          return EVar(k - 1 - j + binder_offset)
        }
      }
      raise PolyElabError::MetaScopeEscape(meta_id, outer_idx)
    }
    EMeta(m, sub_spine) => {
      if m == meta_id {
        raise PolyElabError::MetaOccursCheckFailed(meta_id)
      }
      let mapped : Array[Int32] = []
      for sv in sub_spine {
        if sv < binder_offset {
          mapped.push(sv)
        } else {
          let outer_sv = sv - binder_offset
          let mut found = -1
          for j = 0; j < k; j = j + 1 {
            if spine[j] == outer_sv {
              found = k - 1 - j + binder_offset
            }
          }
          if found < 0 {
            raise PolyElabError::MetaScopeEscape(meta_id, outer_sv)
          }
          mapped.push(found)
        }
      }
      EMeta(m, mapped)
    }
    EPatVar(_) | EUniv(_) | EPolyUniv(_) | EBase(_) => tm
    EPi(imp, x, a, b) =>
      EPi(
        imp,
        x,
        miller_invert(meta_id, spine, a, binder_offset),
        miller_invert(meta_id, spine, b, binder_offset + 1),
      )
    ELam(imp, x, a, b) =>
      ELam(
        imp,
        x,
        miller_invert(meta_id, spine, a, binder_offset),
        miller_invert(meta_id, spine, b, binder_offset + 1),
      )
    EApp(imp, f, a) =>
      EApp(
        imp,
        miller_invert(meta_id, spine, f, binder_offset),
        miller_invert(meta_id, spine, a, binder_offset),
      )
    ESym(s, args) => {
      let out : Array[ElabTm] = []
      for x in args {
        out.push(miller_invert(meta_id, spine, x, binder_offset))
      }
      ESym(s, out)
    }
  }
}

///|
fn solve_miller_pattern(
  store : MetaStore,
  meta_id : Int32,
  spine : Array[Int32],
  rhs : ElabTm,
) -> Unit raise PolyElabError {
  // Check linear distinctness of pattern spine:
  for i = 0; i < spine.length(); i = i + 1 {
    for j = i + 1; j < spine.length(); j = j + 1 {
      if spine[i] == spine[j] {
        raise PolyElabError::NonLinearMetaSpine(meta_id)
      }
    }
  }
  if occurs_in(meta_id, rhs) {
    raise PolyElabError::MetaOccursCheckFailed(meta_id)
  }
  let inv_body = miller_invert(meta_id, spine, rhs, 0)
  store.solutions[meta_id] = (spine.length(), inv_body)
}

///|
/// Theorem 11.2 (Rewrite-Modulo Miller Pattern Unification with Flex-Flex Spine Intersection Pruning):
/// Normalizes both sides modulo `rules` + current `store`, then solves flex-rigid, rigid-flex,
/// flex-flex (Abel-Pientka spine intersection pruning!), and structural rigid-rigid equations!
pub fn unify_modulo_rewrites(
  store : MetaStore,
  rules : Array[ImplicitRewriteRule],
  t1_raw : ElabTm,
  t2_raw : ElabTm,
) -> Unit raise PolyElabError {
  let t1 = rewrite_normalize(rules, store.zonk(t1_raw))
  let t2 = rewrite_normalize(rules, store.zonk(t2_raw))
  if t1 == t2 {
    return
  }
  match (t1, t2) {
    (EMeta(m1, sp1), EMeta(m2, sp2)) =>
      if m1 == m2 {
        // Same metavariable `?m[sp1] =?= ?m[sp2]`: Abel-Pientka Spine Pruning keeps ONLY matching positions!
        let common : Array[Int32] = []
        let kept_pos : Array[Int32] = []
        let len = if sp1.length() <= sp2.length() {
          sp1.length()
        } else {
          sp2.length()
        }
        for i = 0; i < len; i = i + 1 {
          if sp1[i] == sp2[i] {
            common.push(sp1[i])
            kept_pos.push(i)
          }
        }
        let (pruned_id, _) = store.fresh_meta(0)
        let k1 = sp1.length()
        let new_sp : Array[Int32] = []
        for pos in kept_pos {
          new_sp.push(k1 - 1 - pos)
        }
        store.solutions[m1] = (k1, EMeta(pruned_id, new_sp))
      } else {
        solve_miller_pattern(store, m1, sp1, t2)
      }
    (EMeta(m1, sp1), _) => solve_miller_pattern(store, m1, sp1, t2)
    (_, EMeta(m2, sp2)) => solve_miller_pattern(store, m2, sp2, t1)
    (EPi(i1, _, a1, b1), EPi(i2, _, a2, b2)) => {
      if i1 != i2 {
        raise PolyElabError::UnificationSymbolClash(t1, t2)
      }
      unify_modulo_rewrites(store, rules, a1, a2)
      unify_modulo_rewrites(store, rules, b1, b2)
    }
    (ELam(i1, _, a1, b1), ELam(i2, _, a2, b2)) => {
      if i1 != i2 {
        raise PolyElabError::UnificationSymbolClash(t1, t2)
      }
      unify_modulo_rewrites(store, rules, a1, a2)
      unify_modulo_rewrites(store, rules, b1, b2)
    }
    (EApp(i1, f1, a1), EApp(i2, f2, a2)) => {
      if i1 != i2 {
        raise PolyElabError::UnificationSymbolClash(t1, t2)
      }
      unify_modulo_rewrites(store, rules, f1, f2)
      unify_modulo_rewrites(store, rules, a1, a2)
    }
    (ESym(s1, args1), ESym(s2, args2)) => {
      if s1 != s2 || args1.length() != args2.length() {
        raise PolyElabError::UnificationSymbolClash(t1, t2)
      }
      for i = 0; i < args1.length(); i = i + 1 {
        unify_modulo_rewrites(store, rules, args1[i], args2[i])
      }
    }
    _ => raise PolyElabError::UnificationSymbolClash(t1, t2)
  }
}
