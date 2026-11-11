///|
/// Module M10 (Part 1) — Affine & Quantitative Semiring (`Grade`), Galois Residuated Subtraction,
/// and Hardware 64-Bit SWAR 2-Bit-Per-Variable Resource Vector (`UsageVec64`).

///|
pub(all) suberror QTTError {
  ContextVariableOverflow(Int32)
  UnboundQVar(Int32)
  ZeroGradeVariableUsedAtRuntime(Int32)
  ResourceSubsumptionViolation(String, Grade, Grade)
  ExpectedTypeSort(QTerm)
  ExpectedGradedPi(QTerm)
  ExpectedGradedSigma(QTerm)
  ExpectedAdditiveWith(QTerm)
  GradeAnnotationMismatch(Grade, Grade)
  QTypeMismatch(QTerm, QTerm)
}

///|
/// 4-Element Affine-Linear-Erased-Unrestricted Resource Rig:
/// - `GZero`   (`0b00`): Erased / Compile-time only (`0` uses)
/// - `GOne`    (`0b01`): Strict Linear (exactly `1` runtime use)
/// - `GAffine` (`0b10`): Affine (`0` or `1` runtime use; weakening allowed, contraction forbidden)
/// - `GOmega`  (`0b11`): Unrestricted (`0, 1, 2, ...` runtime uses)
#derive(Eq, Hash, Compare, Debug)
pub(all) enum Grade {
  GZero
  GOne
  GAffine
  GOmega
}

///|
pub extend Grade with Eq::{equal, not_equal}

///|
pub extend Grade with Hash::{hash_combine, hash}

///|
pub extend Grade with Compare::{compare, op_lt, op_le, op_ge, op_gt}

///|
pub extend Grade with @debug.Debug::{to_repr}

///|
pub impl Show for Grade with fn output(self, logger) {
  match self {
    GZero => logger.write_string("0")
    GOne => logger.write_string("1")
    GAffine => logger.write_string("<=1")
    GOmega => logger.write_string("ω")
  }
}

///|
pub extend Grade with Show::{to_string, output}

///|
pub fn Grade::to_bits(self : Grade) -> UInt64 {
  match self {
    GZero => 0UL
    GOne => 1UL
    GAffine => 2UL
    GOmega => 3UL
  }
}

///|
pub fn Grade::from_bits(b : UInt64) -> Grade {
  match b & 3UL {
    0UL => GZero
    1UL => GOne
    2UL => GAffine
    _ => GOmega
  }
}

///|
/// Sequential / Multiplicative Addition `g1 + g2`:
/// Using a resource in BOTH `t1` and `t2` sums their runtime multiplicities (`1 + 1 = ω`).
pub fn Grade::add(self : Grade, other : Grade) -> Grade {
  match (self, other) {
    (GZero, x) | (x, GZero) => x
    _ => GOmega
  }
}

///|
/// Context Scaling / Semiring Multiplication `g1 * g2`:
/// `0 * x = 0` (erases all inner uses!), `1 * x = x`, `Affine * Affine = Affine`.
pub fn Grade::mul(self : Grade, other : Grade) -> Grade {
  match (self, other) {
    (GZero, _) | (_, GZero) => GZero
    (GOne, x) | (x, GOne) => x
    (GAffine, GAffine) => GAffine
    _ => GOmega
  }
}

///|
/// Additive Branch / With-Pair Join `g1 ⊔ g2`:
/// Used when ONLY ONE of two branches (`if` or additive `A & B`) executes at runtime!
/// Notice `1 ⊔ 1 = 1` and `1 ⊔ 0 = Affine`!
pub fn Grade::additive_join(self : Grade, other : Grade) -> Grade {
  if self == other {
    return self
  }
  match (self, other) {
    (GZero, GOne) | (GOne, GZero) => GAffine
    (GZero, GAffine) | (GAffine, GZero) => GAffine
    (GOne, GAffine) | (GAffine, GOne) => GAffine
    _ => GOmega
  }
}

///|
/// Sub-usaging Partial Order `actual.subsumed_by(declared)` (`actual ≼ declared`):
/// Holds iff an actual usage `actual` is permitted by a variable bound with grade `declared`!
/// - `declared = 0`      => `actual == 0`
/// - `declared = 1`      => `actual == 1` (strict linear!)
/// - `declared = Affine` => `actual ∈ {0, 1, Affine}` (weakening OK, `ω` forbidden!)
/// - `declared = ω`      => always true!
pub fn Grade::subsumed_by(self : Grade, declared : Grade) -> Bool {
  match declared {
    GZero => self == GZero
    GOne => self == GOne
    GAffine => self != GOmega
    GOmega => true
  }
}

///|
/// Galois Residuated Subtraction `residuated_sub(budget, already)` (Eriksson-Danielsson-Abel TYPES 2025):
/// Returns the least additional usage grade `r` in `[GZero, GOne, GAffine, GOmega]` such that
/// `(already.add(r)).subsumed_by(budget)` holds (or `None` if `already` already exceeded `budget`)!
pub fn Grade::residuated_sub(budget : Grade, already : Grade) -> Grade? {
  let candidates : Array[Grade] = [GZero, GOne, GAffine, GOmega]
  for r in candidates {
    if already.add(r).subsumed_by(budget) {
      return Some(r)
    }
  }
  None
}

///|
/// Hardware 64-Bit SWAR Resource Usage Vector:
/// Packs 32 context variable grades (`2 bits * 32 = 64 bits`) into a single `UInt64` machine word!
/// Level `l` (`0 <= l < 32`) occupies bits `[2*l, 2*l + 1]`.
#derive(Eq, Hash, Compare, Debug)
pub(all) struct UsageVec64 {
  bits : UInt64
}

///|
pub extend UsageVec64 with Eq::{equal, not_equal}

///|
pub extend UsageVec64 with Hash::{hash_combine, hash}

///|
pub extend UsageVec64 with Compare::{compare, op_lt, op_le, op_ge, op_gt}

///|
pub extend UsageVec64 with @debug.Debug::{to_repr}

///|
pub fn UsageVec64::zero() -> UsageVec64 {
  { bits: 0UL, }
}

///|
pub fn UsageVec64::singleton(
  lvl : Int32,
  g : Grade,
) -> UsageVec64 raise QTTError {
  if lvl < 0 || lvl >= 32 {
    raise QTTError::ContextVariableOverflow(lvl)
  }
  { bits: g.to_bits() << (2 * lvl), }
}

///|
pub fn UsageVec64::get(self : UsageVec64, lvl : Int32) -> Grade {
  if lvl < 0 || lvl >= 32 {
    GZero
  } else {
    Grade::from_bits(self.bits >> (2 * lvl))
  }
}

///|
pub fn UsageVec64::clear_slot(self : UsageVec64, lvl : Int32) -> UsageVec64 {
  if lvl < 0 || lvl >= 32 {
    self
  } else {
    let mask = (3UL << (2 * lvl)).lnot()
    { bits: self.bits & mask, }
  }
}

///|
/// O(1) Erasure Fast-Path Scalar Multiplication `g · u`:
/// If `g == GZero`, clears ALL 32 variables to `0UL` in a single register load!
/// If `g == GOne`, returns `self` unchanged in a single register move!
pub fn UsageVec64::scale(self : UsageVec64, g : Grade) -> UsageVec64 {
  match g {
    GZero => { bits: 0UL, }
    GOne => self
    _ => {
      if self.bits == 0UL {
        return { bits: 0UL, }
      }
      let mut out = 0UL
      for l = 0; l < 32; l = l + 1 {
        let cur = self.get(l)
        if cur != GZero {
          out = out | (g.mul(cur).to_bits() << (2 * l))
        }
      }
      { bits: out, }
    }
  }
}

///|
pub fn UsageVec64::add(self : UsageVec64, other : UsageVec64) -> UsageVec64 {
  if self.bits == 0UL {
    return other
  }
  if other.bits == 0UL {
    return self
  }
  // Fast non-overlapping disjoint variable bitmask fast path: `(a_nonzero & b_nonzero) == 0` -> bitwise OR!
  let nz_a = (self.bits | (self.bits >> 1)) & 0x5555555555555555UL
  let nz_b = (other.bits | (other.bits >> 1)) & 0x5555555555555555UL
  if (nz_a & nz_b) == 0UL {
    return { bits: self.bits | other.bits, }
  }
  let mut out = 0UL
  for l = 0; l < 32; l = l + 1 {
    let s = self.get(l).add(other.get(l))
    out = out | (s.to_bits() << (2 * l))
  }
  { bits: out, }
}

///|
pub fn UsageVec64::additive_join(
  self : UsageVec64,
  other : UsageVec64,
) -> UsageVec64 {
  if self.bits == other.bits {
    return self
  }
  let mut out = 0UL
  for l = 0; l < 32; l = l + 1 {
    let j = self.get(l).additive_join(other.get(l))
    out = out | (j.to_bits() << (2 * l))
  }
  { bits: out, }
}
