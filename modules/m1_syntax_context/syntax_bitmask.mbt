///|
/// Module M1 — Intrinsic Bit-Summary Syntax for Dependent Type Theory
/// Implements O(1) 64-bit free-variable occurrence masks, exact binder depth bounds,
/// and 64-bit SplitMix64 structural hashes on every AST node.

///|
pub suberror SyntaxError {
  InvalidDeBruijnIndex(Int32)
  StrengtheningBlocked(Int32)
  InvalidContextPosition(Int32)
  NonIndependentSwap(Int32, Int32)
  UnboundOperadSlot(Int32)
}

///|
#derive(Eq, Debug)
pub(all) enum SynKind {
  Var(Int32)
  Hole(Int32)
  Univ(Int32)
  PolyUniv(Int32, Int32)
  PropSort
  SmallEncode(Int32, SynExpr)
  SmallDecode(Int32, SynExpr)
  Pi(String, SynExpr, SynExpr)
  Lam(String, SynExpr, SynExpr)
  App(SynExpr, SynExpr)
  Sigma(String, SynExpr, SynExpr)
  Pair(SynExpr, SynExpr, SynExpr)
  Fst(SynExpr)
  Snd(SynExpr)
  UnitTy
  UnitVal
  EmptyTy
  Absurd(SynExpr, SynExpr)
  SumTy(SynExpr, SynExpr)
  Inl(SynExpr, SynExpr)
  Inr(SynExpr, SynExpr)
  CaseSum(SynExpr, SynExpr, SynExpr, SynExpr)
  NatTy
  Zero
  Succ(SynExpr)
  NatRec(SynExpr, SynExpr, SynExpr, SynExpr)
  IdTy(SynExpr, SynExpr, SynExpr)
  Refl(SynExpr, SynExpr)
  JElim(SynExpr, SynExpr, SynExpr, SynExpr, SynExpr, SynExpr)
  SquashTy(SynExpr)
  SquashIntro(SynExpr)
  ConstRef(String, Array[Int32])
}

///|
pub extend SynKind with Eq::{equal, not_equal}

///|
pub extend SynKind with @debug.Debug::{to_repr}

///|
#derive(Eq, Debug)
pub(all) struct SynExpr {
  kind : SynKind
  occ_mask : UInt64
  slot_mask : UInt64
  max_free : Int32
  size : Int32
  hash64 : UInt64
}

///|
pub extend SynExpr with Eq::{equal, not_equal}

///|
pub extend SynExpr with @debug.Debug::{to_repr}

///|
fn mix64(z0 : UInt64) -> UInt64 {
  let z1 = (z0 ^ (z0 >> 30)) * 0xBF58476D1CE4E5B9UL
  let z2 = (z1 ^ (z1 >> 27)) * 0x94D049BB133111EBUL
  z2 ^ (z2 >> 31)
}

///|
fn combine_hash(tag : UInt64, h1 : UInt64, h2 : UInt64) -> UInt64 {
  mix64(tag ^ (h1 * 0x9E3779B97F4A7C15UL) ^ mix64(h2 + 0x517CC1B727220A95UL))
}

///|
fn hash_str(s : String) -> UInt64 {
  let mut h : UInt64 = 0xCBF29CE484222325UL
  for c in s {
    h = (h ^ c.to_int().to_uint64()) * 0x100000001B3UL
  }
  mix64(h)
}

///|
fn max_i32(a : Int32, b : Int32) -> Int32 {
  if a >= b {
    a
  } else {
    b
  }
}

///|
fn bind_occ_mask(mask : UInt64, binders : Int32) -> UInt64 {
  if binders <= 0 {
    mask
  } else if binders >= 64 {
    0UL
  } else {
    mask >> binders
  }
}

///|
fn bind_max_free(mf : Int32, binders : Int32) -> Int32 {
  let r = mf - binders
  if r > 0 {
    r
  } else {
    0
  }
}

///|
pub fn mk_var(idx : Int32) -> SynExpr raise SyntaxError {
  if idx < 0 {
    raise SyntaxError::InvalidDeBruijnIndex(idx)
  }
  let bit = if idx < 64 { 1UL << idx } else { 0UL }
  {
    kind: Var(idx),
    occ_mask: bit,
    slot_mask: 0UL,
    max_free: idx + 1,
    size: 1,
    hash64: combine_hash(0x01UL, idx.to_uint64(), 0UL),
  }
}

///|
pub fn mk_var_unchecked(idx : Int32) -> SynExpr {
  let safe_idx = if idx >= 0 { idx } else { 0 }
  let bit = if safe_idx < 64 { 1UL << safe_idx } else { 0UL }
  {
    kind: Var(safe_idx),
    occ_mask: bit,
    slot_mask: 0UL,
    max_free: safe_idx + 1,
    size: 1,
    hash64: combine_hash(0x01UL, safe_idx.to_uint64(), 0UL),
  }
}

///|
pub fn mk_hole(slot : Int32) -> SynExpr {
  let s = if slot >= 0 { slot } else { 0 }
  let sbit = if s < 64 { 1UL << s } else { 1UL << 63 }
  {
    kind: Hole(s),
    occ_mask: 0UL,
    slot_mask: sbit,
    max_free: 0,
    size: 1,
    hash64: combine_hash(0x02UL, s.to_uint64(), 0UL),
  }
}

///|
pub fn mk_univ(level : Int32) -> SynExpr {
  {
    kind: Univ(level),
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: combine_hash(0x03UL, level.to_uint64(), 0UL),
  }
}

///|
pub fn mk_poly_univ(var_id : Int32, offset : Int32) -> SynExpr {
  {
    kind: PolyUniv(var_id, offset),
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: combine_hash(0x04UL, var_id.to_uint64(), offset.to_uint64()),
  }
}

///|
pub fn mk_prop_sort() -> SynExpr {
  {
    kind: PropSort,
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: mix64(0x05UL),
  }
}

///|
pub fn mk_small_encode(level : Int32, ty : SynExpr) -> SynExpr {
  {
    kind: SmallEncode(level, ty),
    occ_mask: ty.occ_mask,
    slot_mask: ty.slot_mask,
    max_free: ty.max_free,
    size: 1 + ty.size,
    hash64: combine_hash(0x06UL, level.to_uint64(), ty.hash64),
  }
}

///|
pub fn mk_small_decode(level : Int32, code : SynExpr) -> SynExpr {
  {
    kind: SmallDecode(level, code),
    occ_mask: code.occ_mask,
    slot_mask: code.slot_mask,
    max_free: code.max_free,
    size: 1 + code.size,
    hash64: combine_hash(0x07UL, level.to_uint64(), code.hash64),
  }
}

///|
pub fn mk_pi(name : String, dom : SynExpr, cod : SynExpr) -> SynExpr {
  {
    kind: Pi(name, dom, cod),
    occ_mask: dom.occ_mask | bind_occ_mask(cod.occ_mask, 1),
    slot_mask: dom.slot_mask | cod.slot_mask,
    max_free: max_i32(dom.max_free, bind_max_free(cod.max_free, 1)),
    size: 1 + dom.size + cod.size,
    hash64: combine_hash(0x08UL, dom.hash64, cod.hash64),
  }
}

///|
pub fn mk_arrow(dom : SynExpr, cod_unshifted : SynExpr) -> SynExpr {
  // Non-dependent function space A -> B encoded as Pi("_", A, shift(1, B))
  let shifted_mask = if cod_unshifted.max_free == 0 {
    0UL
  } else {
    cod_unshifted.occ_mask << 1
  }
  let shifted_mf = if cod_unshifted.max_free == 0 {
    0
  } else {
    cod_unshifted.max_free + 1
  }
  let cod = shift_expr_simple(cod_unshifted, 1, 0)
  let _ = (shifted_mask, shifted_mf)
  mk_pi("_", dom, cod)
}

///|
pub fn mk_lam(name : String, dom : SynExpr, body : SynExpr) -> SynExpr {
  {
    kind: Lam(name, dom, body),
    occ_mask: dom.occ_mask | bind_occ_mask(body.occ_mask, 1),
    slot_mask: dom.slot_mask | body.slot_mask,
    max_free: max_i32(dom.max_free, bind_max_free(body.max_free, 1)),
    size: 1 + dom.size + body.size,
    hash64: combine_hash(0x09UL, dom.hash64, body.hash64),
  }
}

///|
pub fn mk_app(fn_expr : SynExpr, arg : SynExpr) -> SynExpr {
  {
    kind: App(fn_expr, arg),
    occ_mask: fn_expr.occ_mask | arg.occ_mask,
    slot_mask: fn_expr.slot_mask | arg.slot_mask,
    max_free: max_i32(fn_expr.max_free, arg.max_free),
    size: 1 + fn_expr.size + arg.size,
    hash64: combine_hash(0x0AUL, fn_expr.hash64, arg.hash64),
  }
}

///|
pub fn mk_sigma(name : String, fst_ty : SynExpr, snd_ty : SynExpr) -> SynExpr {
  {
    kind: Sigma(name, fst_ty, snd_ty),
    occ_mask: fst_ty.occ_mask | bind_occ_mask(snd_ty.occ_mask, 1),
    slot_mask: fst_ty.slot_mask | snd_ty.slot_mask,
    max_free: max_i32(fst_ty.max_free, bind_max_free(snd_ty.max_free, 1)),
    size: 1 + fst_ty.size + snd_ty.size,
    hash64: combine_hash(0x0BUL, fst_ty.hash64, snd_ty.hash64),
  }
}

///|
pub fn mk_pair(fst : SynExpr, snd : SynExpr, motive_cod : SynExpr) -> SynExpr {
  {
    kind: Pair(fst, snd, motive_cod),
    occ_mask: fst.occ_mask |
    snd.occ_mask |
    bind_occ_mask(motive_cod.occ_mask, 1),
    slot_mask: fst.slot_mask | snd.slot_mask | motive_cod.slot_mask,
    max_free: max_i32(
      max_i32(fst.max_free, snd.max_free),
      bind_max_free(motive_cod.max_free, 1),
    ),
    size: 1 + fst.size + snd.size + motive_cod.size,
    hash64: combine_hash(
      0x0CUL,
      combine_hash(0xC1UL, fst.hash64, snd.hash64),
      motive_cod.hash64,
    ),
  }
}

///|
pub fn mk_fst(p : SynExpr) -> SynExpr {
  {
    kind: Fst(p),
    occ_mask: p.occ_mask,
    slot_mask: p.slot_mask,
    max_free: p.max_free,
    size: 1 + p.size,
    hash64: combine_hash(0x0DUL, p.hash64, 0UL),
  }
}

///|
pub fn mk_snd(p : SynExpr) -> SynExpr {
  {
    kind: Snd(p),
    occ_mask: p.occ_mask,
    slot_mask: p.slot_mask,
    max_free: p.max_free,
    size: 1 + p.size,
    hash64: combine_hash(0x0EUL, p.hash64, 0UL),
  }
}

///|
pub fn mk_unit_ty() -> SynExpr {
  {
    kind: UnitTy,
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: mix64(0x0FUL),
  }
}

///|
pub fn mk_unit_val() -> SynExpr {
  {
    kind: UnitVal,
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: mix64(0x10UL),
  }
}

///|
pub fn mk_empty_ty() -> SynExpr {
  {
    kind: EmptyTy,
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: mix64(0x11UL),
  }
}

///|
pub fn mk_absurd(target_ty : SynExpr, contra : SynExpr) -> SynExpr {
  {
    kind: Absurd(target_ty, contra),
    occ_mask: target_ty.occ_mask | contra.occ_mask,
    slot_mask: target_ty.slot_mask | contra.slot_mask,
    max_free: max_i32(target_ty.max_free, contra.max_free),
    size: 1 + target_ty.size + contra.size,
    hash64: combine_hash(0x12UL, target_ty.hash64, contra.hash64),
  }
}

///|
pub fn mk_sum_ty(left : SynExpr, right : SynExpr) -> SynExpr {
  {
    kind: SumTy(left, right),
    occ_mask: left.occ_mask | right.occ_mask,
    slot_mask: left.slot_mask | right.slot_mask,
    max_free: max_i32(left.max_free, right.max_free),
    size: 1 + left.size + right.size,
    hash64: combine_hash(0x13UL, left.hash64, right.hash64),
  }
}

///|
pub fn mk_inl(sum_ty : SynExpr, v : SynExpr) -> SynExpr {
  {
    kind: Inl(sum_ty, v),
    occ_mask: sum_ty.occ_mask | v.occ_mask,
    slot_mask: sum_ty.slot_mask | v.slot_mask,
    max_free: max_i32(sum_ty.max_free, v.max_free),
    size: 1 + sum_ty.size + v.size,
    hash64: combine_hash(0x14UL, sum_ty.hash64, v.hash64),
  }
}

///|
pub fn mk_inr(sum_ty : SynExpr, v : SynExpr) -> SynExpr {
  {
    kind: Inr(sum_ty, v),
    occ_mask: sum_ty.occ_mask | v.occ_mask,
    slot_mask: sum_ty.slot_mask | v.slot_mask,
    max_free: max_i32(sum_ty.max_free, v.max_free),
    size: 1 + sum_ty.size + v.size,
    hash64: combine_hash(0x15UL, sum_ty.hash64, v.hash64),
  }
}

///|
pub fn mk_case_sum(
  scrut : SynExpr,
  motive : SynExpr,
  on_left : SynExpr,
  on_right : SynExpr,
) -> SynExpr {
  // motive binds 1 (the sum value), on_left binds 1, on_right binds 1
  {
    kind: CaseSum(scrut, motive, on_left, on_right),
    occ_mask: scrut.occ_mask |
    bind_occ_mask(motive.occ_mask, 1) |
    bind_occ_mask(on_left.occ_mask, 1) |
    bind_occ_mask(on_right.occ_mask, 1),
    slot_mask: scrut.slot_mask |
    motive.slot_mask |
    on_left.slot_mask |
    on_right.slot_mask,
    max_free: max_i32(
      max_i32(scrut.max_free, bind_max_free(motive.max_free, 1)),
      max_i32(
        bind_max_free(on_left.max_free, 1),
        bind_max_free(on_right.max_free, 1),
      ),
    ),
    size: 1 + scrut.size + motive.size + on_left.size + on_right.size,
    hash64: combine_hash(
      0x16UL,
      combine_hash(0x61UL, scrut.hash64, motive.hash64),
      combine_hash(0x62UL, on_left.hash64, on_right.hash64),
    ),
  }
}

///|
pub fn mk_nat_ty() -> SynExpr {
  {
    kind: NatTy,
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: mix64(0x17UL),
  }
}

///|
pub fn mk_zero() -> SynExpr {
  {
    kind: Zero,
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: mix64(0x18UL),
  }
}

///|
pub fn mk_succ(n : SynExpr) -> SynExpr {
  {
    kind: Succ(n),
    occ_mask: n.occ_mask,
    slot_mask: n.slot_mask,
    max_free: n.max_free,
    size: 1 + n.size,
    hash64: combine_hash(0x19UL, n.hash64, 0UL),
  }
}

///|
pub fn mk_nat_rec(
  motive : SynExpr,
  base : SynExpr,
  step : SynExpr,
  target : SynExpr,
) -> SynExpr {
  // motive binds 1 (n : Nat); step binds 2 (k : Nat, ih : motive[k])
  {
    kind: NatRec(motive, base, step, target),
    occ_mask: bind_occ_mask(motive.occ_mask, 1) |
    base.occ_mask |
    bind_occ_mask(step.occ_mask, 2) |
    target.occ_mask,
    slot_mask: motive.slot_mask |
    base.slot_mask |
    step.slot_mask |
    target.slot_mask,
    max_free: max_i32(
      max_i32(bind_max_free(motive.max_free, 1), base.max_free),
      max_i32(bind_max_free(step.max_free, 2), target.max_free),
    ),
    size: 1 + motive.size + base.size + step.size + target.size,
    hash64: combine_hash(
      0x1AUL,
      combine_hash(0xA1UL, motive.hash64, base.hash64),
      combine_hash(0xA2UL, step.hash64, target.hash64),
    ),
  }
}

///|
pub fn mk_id_ty(ty : SynExpr, lhs : SynExpr, rhs : SynExpr) -> SynExpr {
  {
    kind: IdTy(ty, lhs, rhs),
    occ_mask: ty.occ_mask | lhs.occ_mask | rhs.occ_mask,
    slot_mask: ty.slot_mask | lhs.slot_mask | rhs.slot_mask,
    max_free: max_i32(ty.max_free, max_i32(lhs.max_free, rhs.max_free)),
    size: 1 + ty.size + lhs.size + rhs.size,
    hash64: combine_hash(
      0x1BUL,
      ty.hash64,
      combine_hash(0xB1UL, lhs.hash64, rhs.hash64),
    ),
  }
}

///|
pub fn mk_refl(ty : SynExpr, x : SynExpr) -> SynExpr {
  {
    kind: Refl(ty, x),
    occ_mask: ty.occ_mask | x.occ_mask,
    slot_mask: ty.slot_mask | x.slot_mask,
    max_free: max_i32(ty.max_free, x.max_free),
    size: 1 + ty.size + x.size,
    hash64: combine_hash(0x1CUL, ty.hash64, x.hash64),
  }
}

///|
pub fn mk_j_elim(
  ty : SynExpr,
  lhs : SynExpr,
  motive : SynExpr,
  refl_case : SynExpr,
  rhs : SynExpr,
  eq_proof : SynExpr,
) -> SynExpr {
  // motive binds 2 (y : A, p : Id(A, lhs, y))
  {
    kind: JElim(ty, lhs, motive, refl_case, rhs, eq_proof),
    occ_mask: ty.occ_mask |
    lhs.occ_mask |
    bind_occ_mask(motive.occ_mask, 2) |
    refl_case.occ_mask |
    rhs.occ_mask |
    eq_proof.occ_mask,
    slot_mask: ty.slot_mask |
    lhs.slot_mask |
    motive.slot_mask |
    refl_case.slot_mask |
    rhs.slot_mask |
    eq_proof.slot_mask,
    max_free: max_i32(
      max_i32(ty.max_free, lhs.max_free),
      max_i32(
        max_i32(bind_max_free(motive.max_free, 2), refl_case.max_free),
        max_i32(rhs.max_free, eq_proof.max_free),
      ),
    ),
    size: 1 +
    ty.size +
    lhs.size +
    motive.size +
    refl_case.size +
    rhs.size +
    eq_proof.size,
    hash64: combine_hash(
      0x1DUL,
      combine_hash(
        0xD1UL,
        ty.hash64,
        combine_hash(0xD2UL, lhs.hash64, motive.hash64),
      ),
      combine_hash(
        0xD3UL,
        refl_case.hash64,
        combine_hash(0xD4UL, rhs.hash64, eq_proof.hash64),
      ),
    ),
  }
}

///|
pub fn mk_squash_ty(inner : SynExpr) -> SynExpr {
  {
    kind: SquashTy(inner),
    occ_mask: inner.occ_mask,
    slot_mask: inner.slot_mask,
    max_free: inner.max_free,
    size: 1 + inner.size,
    hash64: combine_hash(0x1EUL, inner.hash64, 0UL),
  }
}

///|
pub fn mk_squash_intro(witness : SynExpr) -> SynExpr {
  {
    kind: SquashIntro(witness),
    occ_mask: witness.occ_mask,
    slot_mask: witness.slot_mask,
    max_free: witness.max_free,
    size: 1 + witness.size,
    hash64: combine_hash(0x1FUL, witness.hash64, 0UL),
  }
}

///|
pub fn mk_const_ref(name : String, univ_args : Array[Int32]) -> SynExpr {
  let mut h = hash_str(name)
  for u in univ_args {
    h = combine_hash(0x20UL, h, u.to_uint64())
  }
  {
    kind: ConstRef(name, univ_args),
    occ_mask: 0UL,
    slot_mask: 0UL,
    max_free: 0,
    size: 1,
    hash64: h,
  }
}

///|
/// O(1) exact closedness query: returns true iff `expr` has zero free De Bruijn variables.
pub fn SynExpr::is_closed(self : SynExpr) -> Bool {
  self.max_free == 0
}

///|
/// O(1) bitmask check whether De Bruijn index 0 occurs free in `self`
/// (e.g. distinguishes genuine dependent Pi/Sigma from non-dependent Arrow/Product).
pub fn SynExpr::depends_on_var0(self : SynExpr) -> Bool {
  (self.occ_mask & 1UL) != 0UL
}

///|
/// O(1) fast check for free occurrence of De Bruijn index `idx` (exact for idx < 64,
/// exact negative for idx >= max_free, exact recursive fallback only if 64 <= idx < max_free).
pub fn SynExpr::has_free_var(self : SynExpr, idx : Int32) -> Bool {
  if idx < 0 || idx >= self.max_free {
    false
  } else if idx < 64 {
    (self.occ_mask & (1UL << idx)) != 0UL
  } else {
    has_free_var_slow(self, idx)
  }
}

///|
fn has_free_var_slow(e : SynExpr, idx : Int32) -> Bool {
  if idx >= e.max_free {
    return false
  }
  match e.kind {
    Var(i) => i == idx
    Hole(_)
    | Univ(_)
    | PolyUniv(_, _)
    | PropSort
    | UnitTy
    | UnitVal
    | EmptyTy
    | NatTy
    | Zero
    | ConstRef(_, _) => false
    SmallEncode(_, a)
    | SmallDecode(_, a)
    | Fst(a)
    | Snd(a)
    | Succ(a)
    | SquashTy(a)
    | SquashIntro(a) => has_free_var_slow(a, idx)
    Pi(_, a, b) | Lam(_, a, b) | Sigma(_, a, b) =>
      has_free_var_slow(a, idx) || has_free_var_slow(b, idx + 1)
    App(a, b)
    | Absurd(a, b)
    | SumTy(a, b)
    | Inl(a, b)
    | Inr(a, b)
    | Refl(a, b) => has_free_var_slow(a, idx) || has_free_var_slow(b, idx)
    Pair(a, b, c) =>
      has_free_var_slow(a, idx) ||
      has_free_var_slow(b, idx) ||
      has_free_var_slow(c, idx + 1)
    CaseSum(s, m, l, r) =>
      has_free_var_slow(s, idx) ||
      has_free_var_slow(m, idx + 1) ||
      has_free_var_slow(l, idx + 1) ||
      has_free_var_slow(r, idx + 1)
    NatRec(m, z, st, tg) =>
      has_free_var_slow(m, idx + 1) ||
      has_free_var_slow(z, idx) ||
      has_free_var_slow(st, idx + 2) ||
      has_free_var_slow(tg, idx)
    IdTy(t, l, r) =>
      has_free_var_slow(t, idx) ||
      has_free_var_slow(l, idx) ||
      has_free_var_slow(r, idx)
    JElim(t, l, m, rf, r, eqp) =>
      has_free_var_slow(t, idx) ||
      has_free_var_slow(l, idx) ||
      has_free_var_slow(m, idx + 2) ||
      has_free_var_slow(rf, idx) ||
      has_free_var_slow(r, idx) ||
      has_free_var_slow(eqp, idx)
  }
}

///|
/// Shift free variables >= `cutoff` by `delta` (with O(1) short-circuit when max_free <= cutoff).
pub fn shift_expr_simple(e : SynExpr, delta : Int32, cutoff : Int32) -> SynExpr {
  if delta == 0 || e.max_free <= cutoff {
    return e
  }
  match e.kind {
    Var(i) => if i >= cutoff { mk_var_unchecked(i + delta) } else { e }
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
    SmallEncode(l, a) => mk_small_encode(l, shift_expr_simple(a, delta, cutoff))
    SmallDecode(l, a) => mk_small_decode(l, shift_expr_simple(a, delta, cutoff))
    Pi(n, a, b) =>
      mk_pi(
        n,
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff + 1),
      )
    Lam(n, a, b) =>
      mk_lam(
        n,
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff + 1),
      )
    App(a, b) =>
      mk_app(
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff),
      )
    Sigma(n, a, b) =>
      mk_sigma(
        n,
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff + 1),
      )
    Pair(a, b, c) =>
      mk_pair(
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff),
        shift_expr_simple(c, delta, cutoff + 1),
      )
    Fst(a) => mk_fst(shift_expr_simple(a, delta, cutoff))
    Snd(a) => mk_snd(shift_expr_simple(a, delta, cutoff))
    Absurd(a, b) =>
      mk_absurd(
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff),
      )
    SumTy(a, b) =>
      mk_sum_ty(
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff),
      )
    Inl(a, b) =>
      mk_inl(
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff),
      )
    Inr(a, b) =>
      mk_inr(
        shift_expr_simple(a, delta, cutoff),
        shift_expr_simple(b, delta, cutoff),
      )
    CaseSum(s, m, l, r) =>
      mk_case_sum(
        shift_expr_simple(s, delta, cutoff),
        shift_expr_simple(m, delta, cutoff + 1),
        shift_expr_simple(l, delta, cutoff + 1),
        shift_expr_simple(r, delta, cutoff + 1),
      )
    Succ(a) => mk_succ(shift_expr_simple(a, delta, cutoff))
    NatRec(m, z, st, tg) =>
      mk_nat_rec(
        shift_expr_simple(m, delta, cutoff + 1),
        shift_expr_simple(z, delta, cutoff),
        shift_expr_simple(st, delta, cutoff + 2),
        shift_expr_simple(tg, delta, cutoff),
      )
    IdTy(t, l, r) =>
      mk_id_ty(
        shift_expr_simple(t, delta, cutoff),
        shift_expr_simple(l, delta, cutoff),
        shift_expr_simple(r, delta, cutoff),
      )
    Refl(t, x) =>
      mk_refl(
        shift_expr_simple(t, delta, cutoff),
        shift_expr_simple(x, delta, cutoff),
      )
    JElim(t, l, m, rf, r, eqp) =>
      mk_j_elim(
        shift_expr_simple(t, delta, cutoff),
        shift_expr_simple(l, delta, cutoff),
        shift_expr_simple(m, delta, cutoff + 2),
        shift_expr_simple(rf, delta, cutoff),
        shift_expr_simple(r, delta, cutoff),
        shift_expr_simple(eqp, delta, cutoff),
      )
    SquashTy(a) => mk_squash_ty(shift_expr_simple(a, delta, cutoff))
    SquashIntro(a) => mk_squash_intro(shift_expr_simple(a, delta, cutoff))
  }
}

///|
pub impl Show for SynExpr with fn output(self, logger) {
  match self.kind {
    Var(i) => logger.write_string("#\{i}")
    Hole(s) => logger.write_string("?slot\{s}")
    Univ(l) => logger.write_string("U\{l}")
    PolyUniv(v, o) => logger.write_string("U(u\{v}+\{o})")
    PropSort => logger.write_string("Prop")
    SmallEncode(l, a) => {
      logger.write_string("Down\{l}(")
      Show::output(a, logger)
      logger.write_string(")")
    }
    SmallDecode(l, m) => {
      logger.write_string("Up\{l}(")
      Show::output(m, logger)
      logger.write_string(")")
    }
    Pi(n, a, b) =>
      if b.depends_on_var0() {
        logger.write_string("Pi(\{n}:")
        Show::output(a, logger)
        logger.write_string(").")
        Show::output(b, logger)
      } else {
        logger.write_string("(")
        Show::output(a, logger)
        logger.write_string(" -> ")
        Show::output(shift_expr_simple(b, -1, 1), logger)
        logger.write_string(")")
      }
    Lam(n, a, b) => {
      logger.write_string("lam(\{n}:")
      Show::output(a, logger)
      logger.write_string(").")
      Show::output(b, logger)
    }
    App(f, x) => {
      logger.write_string("(")
      Show::output(f, logger)
      logger.write_string(" ")
      Show::output(x, logger)
      logger.write_string(")")
    }
    Sigma(n, a, b) => {
      logger.write_string("Sigma(\{n}:")
      Show::output(a, logger)
      logger.write_string(").")
      Show::output(b, logger)
    }
    Pair(a, b, _) => {
      logger.write_string("<")
      Show::output(a, logger)
      logger.write_string(", ")
      Show::output(b, logger)
      logger.write_string(">")
    }
    Fst(p) => {
      logger.write_string("fst(")
      Show::output(p, logger)
      logger.write_string(")")
    }
    Snd(p) => {
      logger.write_string("snd(")
      Show::output(p, logger)
      logger.write_string(")")
    }
    UnitTy => logger.write_string("Unit")
    UnitVal => logger.write_string("tt")
    EmptyTy => logger.write_string("Empty")
    Absurd(_, c) => {
      logger.write_string("absurd(")
      Show::output(c, logger)
      logger.write_string(")")
    }
    SumTy(a, b) => {
      logger.write_string("(")
      Show::output(a, logger)
      logger.write_string(" + ")
      Show::output(b, logger)
      logger.write_string(")")
    }
    Inl(_, v) => {
      logger.write_string("inl(")
      Show::output(v, logger)
      logger.write_string(")")
    }
    Inr(_, v) => {
      logger.write_string("inr(")
      Show::output(v, logger)
      logger.write_string(")")
    }
    CaseSum(s, _, l, r) => {
      logger.write_string("case(")
      Show::output(s, logger)
      logger.write_string("; ")
      Show::output(l, logger)
      logger.write_string("; ")
      Show::output(r, logger)
      logger.write_string(")")
    }
    NatTy => logger.write_string("Nat")
    Zero => logger.write_string("0")
    Succ(n) => {
      logger.write_string("S(")
      Show::output(n, logger)
      logger.write_string(")")
    }
    NatRec(_, z, st, tg) => {
      logger.write_string("natrec(")
      Show::output(z, logger)
      logger.write_string(", ")
      Show::output(st, logger)
      logger.write_string(", ")
      Show::output(tg, logger)
      logger.write_string(")")
    }
    IdTy(t, l, r) => {
      logger.write_string("Id(")
      Show::output(t, logger)
      logger.write_string(", ")
      Show::output(l, logger)
      logger.write_string(", ")
      Show::output(r, logger)
      logger.write_string(")")
    }
    Refl(_, x) => {
      logger.write_string("refl(")
      Show::output(x, logger)
      logger.write_string(")")
    }
    JElim(_, _, _, rf, _, eqp) => {
      logger.write_string("J(")
      Show::output(rf, logger)
      logger.write_string(", ")
      Show::output(eqp, logger)
      logger.write_string(")")
    }
    SquashTy(a) => {
      logger.write_string("||")
      Show::output(a, logger)
      logger.write_string("||")
    }
    SquashIntro(a) => {
      logger.write_string("|")
      Show::output(a, logger)
      logger.write_string("|")
    }
    ConstRef(c, _) => logger.write_string(c)
  }
}

///|
pub extend SynExpr with Show::{to_string, output}
