///|
/// Module M1 — Strictified Explicit Substitution Calculus (sigma-calculus)
/// Local Axiom (Logical Elimination of Substitutions):
///   Var(0)[t · s] = t
///   Var(n+1)[t · s] = Var(n)[s]
///   e[s] = e in O(1) whenever e.max_free == 0 or (s = Lift(k, _) and e.max_free <= k).

///|
#derive(Eq, Debug)
pub(all) enum Subst {
  Id
  Shift(Int32)
  Cons(SynExpr, Subst)
  Lift(Int32, Subst)
  Comp(Subst, Subst)
}

///|
pub extend Subst with Eq::{equal, not_equal}

///|
pub extend Subst with @debug.Debug::{to_repr}

///|
pub fn subst_id() -> Subst {
  Id
}

///|
/// O(1) smart weakening constructor: Shift(0) collapses to Id.
pub fn subst_shift(k : Int32) -> Subst {
  if k <= 0 {
    Id
  } else {
    Shift(k)
  }
}

///|
/// O(1) extension constructor t · s (with eta collapse Var(0) · Shift(1) == Id).
pub fn subst_cons(head : SynExpr, tail : Subst) -> Subst {
  match (head.kind, tail) {
    (Var(0), Shift(1)) => Id
    _ => Cons(head, tail)
  }
}

///|
/// Single-variable beta substitution [0 := arg] = arg · Id.
pub fn subst_single(arg : SynExpr) -> Subst {
  Cons(arg, Id)
}

///|
/// O(1) binder lifting constructor: Lift(k, Id) == Id, Lift(a, Lift(b, s)) == Lift(a+b, s).
pub fn subst_lift(binders : Int32, s : Subst) -> Subst {
  if binders <= 0 {
    return s
  }
  match s {
    Id => Id
    Lift(inner, base) => Lift(binders + inner, base)
    _ => Lift(binders, s)
  }
}

///|
/// O(1) algebraic smart composition `s1 ∘ s2` (meaning apply s1 first, then s2: e[s1][s2] = e[s1 ∘ s2]).
pub fn subst_compose(s1 : Subst, s2 : Subst) -> Subst {
  match (s1, s2) {
    (Id, _) => s2
    (_, Id) => s1
    (Shift(a), Shift(b)) => subst_shift(a + b)
    (Shift(1), Cons(_, tail)) => tail
    (Shift(k), Cons(_, tail)) =>
      if k > 1 {
        subst_compose(subst_shift(k - 1), tail)
      } else {
        tail
      }
    (Cons(h, t), r) => subst_cons(apply_subst(h, r), subst_compose(t, r))
    (Comp(a, b), c) => Comp(a, subst_compose(b, c))
    _ => Comp(s1, s2)
  }
}

///|
/// Resolve De Bruijn index `idx` under explicit substitution `s`.
pub fn lookup_subst(s : Subst, idx : Int32) -> SynExpr {
  match s {
    Id => mk_var_unchecked(idx)
    Shift(k) => mk_var_unchecked(idx + k)
    Cons(head, tail) =>
      if idx == 0 {
        head
      } else {
        lookup_subst(tail, idx - 1)
      }
    Lift(k, inner) =>
      if idx < k {
        mk_var_unchecked(idx)
      } else {
        shift_expr_simple(lookup_subst(inner, idx - k), k, 0)
      }
    Comp(s1, s2) => apply_subst(lookup_subst(s1, idx), s2)
  }
}

///|
fn is_identity_upto(s : Subst, max_free : Int32) -> Bool {
  if max_free <= 0 {
    return true
  }
  match s {
    Id => true
    Shift(0) => true
    Lift(k, inner) =>
      if max_free <= k {
        true
      } else {
        is_identity_upto(inner, max_free - k)
      }
    _ => false
  }
}

///|
/// Apply explicit substitution `s` to expression `e`, using O(1) max_free & Lift short-circuits.
pub fn apply_subst(e : SynExpr, s : Subst) -> SynExpr {
  if is_identity_upto(s, e.max_free) {
    return e
  }
  match s {
    Shift(k) => shift_expr_simple(e, k, 0)
    Lift(c, Shift(k)) => shift_expr_simple(e, k, c)
    _ => apply_subst_rec(e, s)
  }
}

///|
fn apply_subst_rec(e : SynExpr, s : Subst) -> SynExpr {
  if is_identity_upto(s, e.max_free) {
    return e
  }
  match e.kind {
    Var(i) => lookup_subst(s, i)
    Hole(_)
    | Univ(_)
    | PolyUniv(_, _)
    | PropSort
    | UnitTy
    | UnitVal
    | EmptyTy
    | NatTy
    | Zero
    | ConstRef(_, _) => e
    SmallEncode(l, a) => mk_small_encode(l, apply_subst(a, s))
    SmallDecode(l, a) => mk_small_decode(l, apply_subst(a, s))
    Pi(n, a, b) => mk_pi(n, apply_subst(a, s), apply_subst(b, subst_lift(1, s)))
    Lam(n, a, b) =>
      mk_lam(n, apply_subst(a, s), apply_subst(b, subst_lift(1, s)))
    App(a, b) => mk_app(apply_subst(a, s), apply_subst(b, s))
    Sigma(n, a, b) =>
      mk_sigma(n, apply_subst(a, s), apply_subst(b, subst_lift(1, s)))
    Pair(a, b, c) =>
      mk_pair(
        apply_subst(a, s),
        apply_subst(b, s),
        apply_subst(c, subst_lift(1, s)),
      )
    Fst(a) => mk_fst(apply_subst(a, s))
    Snd(a) => mk_snd(apply_subst(a, s))
    Absurd(a, b) => mk_absurd(apply_subst(a, s), apply_subst(b, s))
    SumTy(a, b) => mk_sum_ty(apply_subst(a, s), apply_subst(b, s))
    Inl(a, b) => mk_inl(apply_subst(a, s), apply_subst(b, s))
    Inr(a, b) => mk_inr(apply_subst(a, s), apply_subst(b, s))
    CaseSum(sc, m, l, r) => {
      let s1 = subst_lift(1, s)
      mk_case_sum(
        apply_subst(sc, s),
        apply_subst(m, s1),
        apply_subst(l, s1),
        apply_subst(r, s1),
      )
    }
    Succ(a) => mk_succ(apply_subst(a, s))
    NatRec(m, z, st, tg) =>
      mk_nat_rec(
        apply_subst(m, subst_lift(1, s)),
        apply_subst(z, s),
        apply_subst(st, subst_lift(2, s)),
        apply_subst(tg, s),
      )
    IdTy(t, l, r) =>
      mk_id_ty(apply_subst(t, s), apply_subst(l, s), apply_subst(r, s))
    Refl(t, x) => mk_refl(apply_subst(t, s), apply_subst(x, s))
    JElim(t, l, m, rf, r, eqp) =>
      mk_j_elim(
        apply_subst(t, s),
        apply_subst(l, s),
        apply_subst(m, subst_lift(2, s)),
        apply_subst(rf, s),
        apply_subst(r, s),
        apply_subst(eqp, s),
      )
    SquashTy(a) => mk_squash_ty(apply_subst(a, s))
    SquashIntro(a) => mk_squash_intro(apply_subst(a, s))
  }
}

///|
/// Strengthen an expression across variable at `cutoff` (decrementing free indices > cutoff),
/// failing with `StrengtheningBlocked` if `cutoff` occurs free in `e` (checked in O(1) via occ_mask!).
pub fn try_strengthen_expr(
  e : SynExpr,
  cutoff : Int32,
) -> SynExpr raise SyntaxError {
  if e.max_free <= cutoff {
    return e
  }
  if e.has_free_var(cutoff) {
    raise SyntaxError::StrengtheningBlocked(cutoff)
  }
  shift_expr_simple(e, -1, cutoff + 1)
}
