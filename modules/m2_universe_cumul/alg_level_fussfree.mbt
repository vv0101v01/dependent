///|
/// Module M2 — Algebraic Universe Expressions & Sterbac-Sterling (2026)
/// Fuss-Free Cumulative Universes vs Jiang-Hu-Oliveira (ICFP 2025) Non-Cumulativity.

///|
pub suberror UniverseError {
  NegativeConcreteLevel(Int32)
  InvalidUniverseVar(Int32)
  UniverseCycleDetected(Array[Int32])
  NonCumulativeMismatch(AlgLevel, AlgLevel)
  CumulativeEntailmentFailed(AlgLevel, AlgLevel)
  LargeEliminationForbidden
}

///|
/// Canonical Algebraic Universe Level:
/// Represents `max( {const_floor} ∪ { u_i + offset_i | (u_i, offset_i) ∈ var_offsets } )`
/// where `const_floor >= 0`, `var_offsets` is sorted strictly by `u_i >= 0`, and `offset_i >= 0`.
#derive(Eq, Debug)
pub(all) struct AlgLevel {
  const_floor : Int32
  var_offsets : Array[(Int32, Int32)]
}

///|
pub extend AlgLevel with Eq::{equal, not_equal}

///|
pub extend AlgLevel with @debug.Debug::{to_repr}

///|
pub fn AlgLevel::zero() -> AlgLevel {
  { const_floor: 0, var_offsets: [], }
}

///|
pub fn AlgLevel::concrete(k : Int32) -> AlgLevel raise UniverseError {
  if k < 0 {
    raise UniverseError::NegativeConcreteLevel(k)
  }
  { const_floor: k, var_offsets: [], }
}

///|
pub fn AlgLevel::concrete_clamped(k : Int32) -> AlgLevel {
  let c = if k >= 0 { k } else { 0 }
  { const_floor: c, var_offsets: [], }
}

///|
pub fn AlgLevel::var_offset(
  var_id : Int32,
  offset : Int32,
) -> AlgLevel raise UniverseError {
  if var_id < 0 {
    raise UniverseError::InvalidUniverseVar(var_id)
  }
  let safe_off = if offset >= 0 { offset } else { 0 }
  { const_floor: safe_off, var_offsets: [(var_id, safe_off)], }
}

///|
/// Canonicalize raw `(const_floor, raw_pairs)` by sorting by `var_id`, merging duplicates via `max`,
/// and raising `const_floor` to at least `max(offset_i)` since every `u_i >= 0` implies `u_i + offset_i >= offset_i`.
pub fn AlgLevel::normalize(
  floor : Int32,
  pairs : Array[(Int32, Int32)],
) -> AlgLevel {
  let mut cf = if floor >= 0 { floor } else { 0 }
  let map : Map[Int32, Int32] = Map([])
  let vars : Array[Int32] = []
  for item in pairs {
    let (v, off0) = item
    if v >= 0 {
      let off = if off0 >= 0 { off0 } else { 0 }
      if off > cf {
        cf = off
      }
      match map.get(v) {
        Some(prev) => if off > prev { map[v] = off }
        None => {
          map[v] = off
          vars.push(v)
        }
      }
    }
  }
  vars.sort()
  let merged : Array[(Int32, Int32)] = []
  for v in vars {
    match map.get(v) {
      Some(off) => merged.push((v, off))
      None => ()
    }
  }
  { const_floor: cf, var_offsets: merged, }
}

///|
/// Successor operation `ℓ + 1` distributing over `max`:
/// `(max(c, u_i + k_i)) + 1 = max(c + 1, u_i + (k_i + 1))` except pure constant `[0] + 1 = [1]`.
pub fn AlgLevel::succ(self : AlgLevel) -> AlgLevel {
  if self.var_offsets.is_empty() {
    { const_floor: self.const_floor + 1, var_offsets: [], }
  } else {
    let bumped : Array[(Int32, Int32)] = []
    for item in self.var_offsets {
      let (v, off) = item
      bumped.push((v, off + 1))
    }
    AlgLevel::normalize(self.const_floor + 1, bumped)
  }
}

///|
/// Least upper bound `max(ℓ_1, ℓ_2)` in the free inflationary semilattice.
pub fn AlgLevel::lub(self : AlgLevel, other : AlgLevel) -> AlgLevel {
  let floor = if self.const_floor >= other.const_floor {
    self.const_floor
  } else {
    other.const_floor
  }
  let combined = self.var_offsets.copy()
  for item in other.var_offsets {
    combined.push(item)
  }
  AlgLevel::normalize(floor, combined)
}

///|
/// Evaluate `AlgLevel` under a concrete natural-number valuation `val_fn(u) >= 0`.
pub fn AlgLevel::eval_with(self : AlgLevel, valuation : Array[Int32]) -> Int32 {
  let mut best = self.const_floor
  for item in self.var_offsets {
    let (v, off) = item
    let v_val = if v >= 0 && v < valuation.length() {
      let x = valuation[v]
      if x >= 0 {
        x
      } else {
        0
      }
    } else {
      0
    }
    let cand = v_val + off
    if cand > best {
      best = cand
    }
  }
  best
}

///|
/// Substitute polymorphic universe variable `target_var` with algebraic expression `replacement`.
pub fn AlgLevel::subst_var(
  self : AlgLevel,
  target_var : Int32,
  replacement : AlgLevel,
) -> AlgLevel {
  let mut floor = self.const_floor
  let kept : Array[(Int32, Int32)] = []
  for item in self.var_offsets {
    let (v, off) = item
    if v == target_var {
      let shifted_floor = replacement.const_floor + off
      if shifted_floor > floor {
        floor = shifted_floor
      }
      for r_item in replacement.var_offsets {
        let (rv, roff) = r_item
        kept.push((rv, roff + off))
      }
    } else {
      kept.push((v, off))
    }
  }
  AlgLevel::normalize(floor, kept)
}

///|
pub impl Show for AlgLevel with fn output(self, logger) {
  if self.var_offsets.is_empty() {
    logger.write_string("\{self.const_floor}")
  } else if self.var_offsets.length() == 1 &&
    self.const_floor == self.var_offsets[0].1 {
    let (v, off) = self.var_offsets[0]
    if off == 0 {
      logger.write_string("u\{v}")
    } else {
      logger.write_string("u\{v}+\{off}")
    }
  } else {
    logger.write_string("max(\{self.const_floor}")
    for item in self.var_offsets {
      let (v, off) = item
      if off == 0 {
        logger.write_string(", u\{v}")
      } else {
        logger.write_string(", u\{v}+\{off}")
      }
    }
    logger.write_string(")")
  }
}

///|
pub extend AlgLevel with Show::{to_string, output}

///|
/// Universe Hierarchy Mode (Jiang-Hu-Oliveira ICFP 2025 vs Sterbac-Sterling POPL '27)
#derive(Eq, Debug)
pub(all) enum HierarchyMode {
  Cumulative
  NonCumulative
}

///|
pub extend HierarchyMode with Eq::{equal, not_equal}

///|
pub extend HierarchyMode with @debug.Debug::{to_repr}

///|
/// Parametric Universe Variance Semilattice (Sozeau-Bezem TYPES 2025 / RocqPL 2026)
#derive(Eq, Debug)
pub(all) enum Variance {
  Irrelevant
  Covariant
  Invariant
}

///|
pub extend Variance with Eq::{equal, not_equal}

///|
pub extend Variance with @debug.Debug::{to_repr}

///|
/// Join in Variance Semilattice: Irrelevant < Covariant < Invariant.
pub fn Variance::join(self : Variance, other : Variance) -> Variance {
  match (self, other) {
    (Invariant, _) | (_, Invariant) => Invariant
    (Covariant, _) | (_, Covariant) => Covariant
    (Irrelevant, Irrelevant) => Irrelevant
  }
}

///|
/// Sequential composition of variances through nested parameterized type constructors.
pub fn Variance::compose(outer : Variance, inner : Variance) -> Variance {
  match (outer, inner) {
    (Irrelevant, _) | (_, Irrelevant) => Irrelevant
    (Invariant, _) | (_, Invariant) => Invariant
    (Covariant, Covariant) => Covariant
  }
}

///|
/// Sterbac & Sterling (2026, arXiv:2607.11329v2) Fuss-Free Synthetic Smallness Calculus:
/// Distinguishes Type Shapes (`FussType`) and Universe Code Terms (`FussCode`) mediated SOLELY
/// by `FussEncode` (`⇓_i A : U_i`) and `FussDecode` (`⇑_i M type`).
#derive(Eq, Debug)
pub(all) enum FussType {
  FTBase(AlgLevel)
  FTProp
  FTUniv(AlgLevel)
  FTPi(FussType, FussType)
  FTSigma(FussType, FussType)
  FTSum(FussType, FussType)
  FTId(FussType)
  FTDecode(AlgLevel, FussCode)
}

///|
pub extend FussType with Eq::{equal, not_equal}

///|
pub extend FussType with @debug.Debug::{to_repr}

///|
#derive(Eq, Debug)
pub(all) enum FussCode {
  FCVar(String, AlgLevel)
  FCEncode(AlgLevel, FussType)
}

///|
pub extend FussCode with Eq::{equal, not_equal}

///|
pub extend FussCode with @debug.Debug::{to_repr}

///|
/// Derived Fuss-Free Cumulative Lift `↑_i^j(M) := ⇓_j(⇑_i(M))` (Sterbac & Sterling §1.2.2).
pub fn fuss_derived_lift(
  src_lvl : AlgLevel,
  dst_lvl : AlgLevel,
  code : FussCode,
) -> FussCode {
  FCEncode(dst_lvl, FTDecode(src_lvl, code))
}

///|
/// Local Axiom (Logical Elimination `univ-beta` & `univ-eta/ext`):
///   `⇑_i (⇓_i A) -> A` and `⇓_i (⇑_i M) -> M` when M already has exact level `i`.
/// Collapses arbitrarily nested cumulative lift chains `↑_j^k (↑_i^j M) -> ↑_i^k M` automatically!
pub fn normalize_fuss_type(ty : FussType) -> FussType {
  match ty {
    FTBase(_) | FTProp | FTUniv(_) => ty
    FTPi(a, b) => FTPi(normalize_fuss_type(a), normalize_fuss_type(b))
    FTSigma(a, b) => FTSigma(normalize_fuss_type(a), normalize_fuss_type(b))
    FTSum(a, b) => FTSum(normalize_fuss_type(a), normalize_fuss_type(b))
    FTId(a) => FTId(normalize_fuss_type(a))
    FTDecode(lvl, code) =>
      match normalize_fuss_code(code) {
        FCEncode(_, inner_ty) => inner_ty
        norm_c => FTDecode(lvl, norm_c)
      }
  }
}

///|
pub fn normalize_fuss_code(code : FussCode) -> FussCode {
  match code {
    FCVar(_, _) => code
    FCEncode(target_lvl, ty) =>
      match normalize_fuss_type(ty) {
        FTDecode(src_lvl, inner_c) =>
          if src_lvl == target_lvl {
            inner_c
          } else {
            FCEncode(target_lvl, FTDecode(src_lvl, inner_c))
          }
        norm_ty => FCEncode(target_lvl, norm_ty)
      }
  }
}

///|
/// Synthesize the least algebraic universe level `ℓ` such that `Γ ⊢ A small_ℓ` holds:
/// - `FTProp` is `small_0` (or lives in U_0 as a type code: `Prop : U_0`, inhabitants small_0)
/// - `FTUniv(i)` has least smallness `i + 1` (`univ-small`: `i < j <=> i + 1 <= j`)
/// - `FTPi(A, B)` / `FTSigma(A, B)` / `FTSum(A, B)` has least smallness `lub(small(A), small(B))`
/// - `FTDecode(i, _)` has least smallness `i` (`univ-elim-small`).
pub fn synthesize_least_smallness(ty : FussType) -> AlgLevel {
  match ty {
    FTBase(l) => l
    FTProp => AlgLevel::zero()
    FTUniv(l) => l.succ()
    FTPi(a, b) | FTSigma(a, b) | FTSum(a, b) =>
      synthesize_least_smallness(a).lub(synthesize_least_smallness(b))
    FTId(a) => synthesize_least_smallness(a)
    FTDecode(l, _) => l
  }
}

///|
/// Verify Impredicative Prop / Large Elimination Safety Criterion:
/// Eliminating a `Prop` proof into a computational universe `Type_i` is forbidden for
/// multi-constructor propositions (prevents Hurkens/Coquand inconsistency), allowed into `Prop`.
pub fn check_prop_elimination(
  scrutinee_is_prop : Bool,
  is_singleton_or_empty : Bool,
  motive_is_prop : Bool,
) -> Unit raise UniverseError {
  if scrutinee_is_prop && !motive_is_prop && !is_singleton_or_empty {
    raise UniverseError::LargeEliminationForbidden
  }
}
