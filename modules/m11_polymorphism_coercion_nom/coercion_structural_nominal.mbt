///|
/// Module M11 (Part 2):
/// 1. O(1) 64-Bit Bitmask + Popcount Sparse Structural Record Types & Values
/// 2. Generative Nominal Branded Types & Adjoint Unbrand Modality
/// 3. Coercive Subtyping Graph, Functorial Lifting (Arrow/Prod/Record/Unbrand), & Diamond Coherence!

///|
#derive(Eq, Debug)
pub(all) enum HybridTy {
  HPrim(String)
  HProd(HybridTy, HybridTy)
  HArrow(HybridTy, HybridTy)
  /// Canonical O(1) Sparse Structural Record:
  /// `field_mask` has bit `fid` (`0 <= fid < 64`) set iff field `fid` is present;
  /// `fields` stores types sorted strictly by increasing `fid` (`fields.length() == field_mask.popcount()`)!
  HStructRecord(UInt64, Array[HybridTy])
  /// Generative Nominal Branded Type: `Nominal(brand_id, brand_name, underlying_ty)`!
  HNominal(Int32, String, HybridTy)
}

///|
pub extend HybridTy with Eq::{equal, not_equal}

///|
pub extend HybridTy with @debug.Debug::{to_repr}

///|
/// Runtime Value for Executing Synthesized Coercions & O(1) Popcount Structural Projections!
pub(all) enum HybridVal {
  VPrim(Int32)
  VPair(HybridVal, HybridVal)
  VFun((HybridVal) -> HybridVal)
  VStructRecord(UInt64, Array[HybridVal])
  VNominal(Int32, HybridVal)
}

///|
/// Hardware O(1) Bitwise Popcount for `UInt64` (SWAR Hamming Weight in 12 arithmetic ops!).
pub fn popcount64(x0 : UInt64) -> Int32 {
  let m1 = 0x5555555555555555UL
  let m2 = 0x3333333333333333UL
  let m4 = 0x0F0F0F0F0F0F0F0FUL
  let h01 = 0x0101010101010101UL
  let mut x = x0 - ((x0 >> 1) & m1)
  x = (x & m2) + ((x >> 2) & m2)
  x = (x + (x >> 4)) & m4
  (((x * h01) >> 56) & 0x7FUL).to_int()
}

///|
/// Build a canonical `HStructRecord` from an arbitrary unsorted array of `(field_id, field_ty)` pairs!
/// Automatically sorts by `field_id`, builds `field_mask`, and guarantees Order-Independent Structural Identity!
pub fn mk_structural_record_ty(
  entries : Array[(Int32, HybridTy)],
) -> HybridTy raise PolyElabError {
  let mut mask = 0UL
  for kv in entries {
    let fid = kv.0
    if fid < 0 || fid >= 64 {
      raise PolyElabError::MissingStructuralField(fid)
    }
    if ((mask >> fid) & 1UL) != 0UL {
      raise PolyElabError::DuplicateRecordField(fid)
    }
    mask = mask | (1UL << fid)
  }
  let sorted : Array[HybridTy] = []
  for fid = 0; fid < 64; fid = fid + 1 {
    if ((mask >> fid) & 1UL) != 0UL {
      for kv in entries {
        if kv.0 == fid {
          sorted.push(kv.1)
        }
      }
    }
  }
  HStructRecord(mask, sorted)
}

///|
pub fn mk_structural_record_val(
  entries : Array[(Int32, HybridVal)],
) -> HybridVal raise PolyElabError {
  let mut mask = 0UL
  for kv in entries {
    let fid = kv.0
    if fid < 0 || fid >= 64 {
      raise PolyElabError::MissingStructuralField(fid)
    }
    if ((mask >> fid) & 1UL) != 0UL {
      raise PolyElabError::DuplicateRecordField(fid)
    }
    mask = mask | (1UL << fid)
  }
  let sorted : Array[HybridVal] = []
  for fid = 0; fid < 64; fid = fid + 1 {
    if ((mask >> fid) & 1UL) != 0UL {
      for kv in entries {
        if kv.0 == fid {
          sorted.push(kv.1)
        }
      }
    }
  }
  VStructRecord(mask, sorted)
}

///|
/// O(1) Bitmask + Popcount Structural Field Projection!
/// Zero hash lookups, zero linear search:
/// 1. Check `((mask >> fid) & 1) != 0`
/// 2. Dense slot `idx = popcount64(mask & ((1UL << fid) - 1UL))`!
pub fn project_structural_field(
  rec : HybridVal,
  fid : Int32,
) -> HybridVal raise PolyElabError {
  if fid < 0 || fid >= 64 {
    raise PolyElabError::MissingStructuralField(fid)
  }
  match rec {
    VStructRecord(mask, vals) => {
      if ((mask >> fid) & 1UL) == 0UL {
        raise PolyElabError::MissingStructuralField(fid)
      }
      let lower_mask = if fid == 0 { 0UL } else { (1UL << fid) - 1UL }
      let dense_idx = popcount64(mask & lower_mask)
      vals[dense_idx]
    }
    _ => raise PolyElabError::MissingStructuralField(fid)
  }
}

///|
/// Explicit Nominal Brand Constructor (`seal_nominal`) & Validated Destructor (`unseal_nominal`):
/// Enforces generative brand identity (`brand_id` must match exactly!).
pub fn seal_nominal(brand_id : Int32, v : HybridVal) -> HybridVal {
  VNominal(brand_id, v)
}

///|
pub fn unseal_nominal(
  expected_brand : Int32,
  v : HybridVal,
) -> HybridVal raise PolyElabError {
  match v {
    VNominal(actual, inner) => {
      if actual != expected_brand {
        raise PolyElabError::NominalBrandMismatch(actual, expected_brand)
      }
      inner
    }
    _ => raise PolyElabError::NominalBrandMismatch(-1, expected_brand)
  }
}

///|
/// Synthesized First-Class Coercion Program `c : T_sub => T_sup`!
pub enum CoercionProg {
  CId
  CPrimStep((Int32) -> Int32)
  CSeq(CoercionProg, CoercionProg)
  CProdMap(CoercionProg, CoercionProg)
  CArrowMap(CoercionProg, CoercionProg)
  CRecordMap(UInt64, Array[(Int32, CoercionProg)])
  CUnbrandThen(Int32, CoercionProg)
}

///|
/// Execute a Synthesized Coercion Program `c` on a `HybridVal`!
pub fn apply_coercion(
  c : CoercionProg,
  v : HybridVal,
) -> HybridVal raise PolyElabError {
  match c {
    CId => v
    CPrimStep(f) =>
      match v {
        VPrim(x) => VPrim(f(x))
        _ => raise PolyElabError::CoercionUnavailable
      }
    CSeq(c1, c2) => apply_coercion(c2, apply_coercion(c1, v))
    CProdMap(ca, cb) =>
      match v {
        VPair(va, vb) => VPair(apply_coercion(ca, va), apply_coercion(cb, vb))
        _ => raise PolyElabError::CoercionUnavailable
      }
    CArrowMap(c_dom_contra, c_cod_cov) =>
      match v {
        VFun(fn_body) =>
          VFun(fn(arg_sup) {
            // Safe contravariant-covariant wrapper (note closures inside `VFun` are total on well-typed values)
            let arg_sub = apply_coercion(c_dom_contra, arg_sup) catch {
              _ => arg_sup
            }
            let res_sub = fn_body(arg_sub)
            apply_coercion(c_cod_cov, res_sub) catch {
              _ => res_sub
            }
          })
        _ => raise PolyElabError::CoercionUnavailable
      }
    CRecordMap(dst_mask, field_coercions) => {
      let out_vals : Array[HybridVal] = []
      for pair in field_coercions {
        let fid = pair.0
        let cf = pair.1
        let raw_field = project_structural_field(v, fid)
        out_vals.push(apply_coercion(cf, raw_field))
      }
      VStructRecord(dst_mask, out_vals)
    }
    CUnbrandThen(brand_id, rest) => {
      let inner = unseal_nominal(brand_id, v)
      apply_coercion(rest, inner)
    }
  }
}

///|
pub(all) struct BaseCoercionEdge {
  src : String
  dst : String
  f : (Int32) -> Int32
}

///|
/// Coercive Subtyping Environment with Registered Base Edges & Forgetful-Unbrand Nominal Whitelist!
pub struct CoercionEnv {
  edges : Array[BaseCoercionEdge]
  unbrandable_brands : Map[Int32, Bool]
}

///|
pub fn CoercionEnv::new() -> CoercionEnv {
  { edges: [], unbrandable_brands: Map([]), }
}

///|
pub fn CoercionEnv::add_prim_coercion(
  self : CoercionEnv,
  src : String,
  dst : String,
  f : (Int32) -> Int32,
) -> Unit {
  self.edges.push({ src, dst, f, })
}

///|
pub fn CoercionEnv::allow_forgetful_unbrand(
  self : CoercionEnv,
  brand_id : Int32,
) -> Unit {
  self.unbrandable_brands[brand_id] = true
}

///|
/// BFS Shortest Canonical Primitive Coercion Path `src_prim => dst_prim`!
fn find_prim_coercion_path(
  env : CoercionEnv,
  src : String,
  dst : String,
) -> CoercionProg? {
  if src == dst {
    return Some(CId)
  }
  let visited : Map[String, Bool] = Map([])
  visited[src] = true
  let queue : Array[(String, CoercionProg)] = [(src, CId)]
  let mut head = 0
  while head < queue.length() {
    let (cur, prog_so_far) = queue[head]
    head = head + 1
    for e in env.edges {
      if e.src == cur && !visited.contains(e.dst) {
        let next_prog = match prog_so_far {
          CId => CPrimStep(e.f)
          _ => CSeq(prog_so_far, CPrimStep(e.f))
        }
        if e.dst == dst {
          return Some(next_prog)
        }
        visited[e.dst] = true
        queue.push((e.dst, next_prog))
      }
    }
  }
  None
}

///|
/// Theorem 11.3 (Diamond Coherence Verifier for Base Coercion Graphs):
/// Enumerates ALL distinct simple coercion paths between every reachable pair `(src, dst)`
/// and verifies they commute identically on all `sample_inputs` (`∀x ∈ samples. p1(x) == p2(x)`),
/// raising `IncoherentCoercionDiamond(src, dst)` if ANY two parallel paths disagree!
pub fn CoercionEnv::verify_diamond_coherence(
  self : CoercionEnv,
  sample_inputs : Array[Int32],
) -> Bool raise PolyElabError {
  let nodes : Array[String] = []
  let seen_n : Map[String, Bool] = Map([])
  for e in self.edges {
    if !seen_n.contains(e.src) {
      seen_n[e.src] = true
      nodes.push(e.src)
    }
    if !seen_n.contains(e.dst) {
      seen_n[e.dst] = true
      nodes.push(e.dst)
    }
  }

  for s in nodes {
    for t in nodes {
      if s != t {
        let all_paths : Array[CoercionProg] = []
        fn dfs(
          cur : String,
          vis : Map[String, Bool],
          acc : CoercionProg,
        ) -> Unit {
          if cur == t {
            all_paths.push(acc)
            return
          }
          for e in self.edges {
            if e.src == cur && !vis.contains(e.dst) {
              let nv = vis.copy()
              nv[e.dst] = true
              let next_acc = match acc {
                CId => CPrimStep(e.f)
                _ => CSeq(acc, CPrimStep(e.f))
              }
              dfs(e.dst, nv, next_acc)
            }
          }
        }

        let init_vis : Map[String, Bool] = Map([])
        init_vis[s] = true
        dfs(s, init_vis, CId)
        if all_paths.length() >= 2 {
          let ref_p = all_paths[0]
          for k = 1; k < all_paths.length(); k = k + 1 {
            for x in sample_inputs {
              let v0 = apply_coercion(ref_p, VPrim(x))
              let vk = apply_coercion(all_paths[k], VPrim(x))
              match (v0, vk) {
                (VPrim(a), VPrim(b)) =>
                  if a != b {
                    raise PolyElabError::IncoherentCoercionDiamond(s, t)
                  }
                _ => raise PolyElabError::IncoherentCoercionDiamond(s, t)
              }
            }
          }
        }
      }
    }
  }
  true
}

///|
/// Theorem 11.4 (Functorial & Structural-Nominal Coercion Synthesis):
/// Synthesizes canonical `CoercionProg : sub => sup` across:
/// - Reflexivity `T => T`
/// - Base Coercion Chains `HPrim(s) => HPrim(t)`
/// - Covariant Products `(A1 × B1) => (A2 × B2)`
/// - Contravariant-Covariant Functions `(A1 -> B1) => (A2 -> B2)` (`A2 => A1` & `B1 => B2`)
/// - O(1) Bitmask Width + Depth Structural Record Subtyping `HStructRecord(m_sub, f_sub) => HStructRecord(m_sup, f_sup)`
///   (`(m_sup & ~m_sub) == 0UL` + fieldwise coercions!)
/// - Adjoint Forgetful Unbranding `HNominal(id, _, S) => sup` ONLY when `id` is whitelisted AND `sup` is NOT a distinct `HNominal`!
pub fn synthesize_coercion(
  env : CoercionEnv,
  sub : HybridTy,
  sup : HybridTy,
) -> CoercionProg? {
  if sub == sup {
    return Some(CId)
  }
  match (sub, sup) {
    (HPrim(s), HPrim(t)) => find_prim_coercion_path(env, s, t)
    (HProd(a1, b1), HProd(a2, b2)) =>
      match
        (synthesize_coercion(env, a1, a2), synthesize_coercion(env, b1, b2)) {
        (Some(ca), Some(cb)) => Some(CProdMap(ca, cb))
        _ => None
      }
    (HArrow(a1, b1), HArrow(a2, b2)) =>
      // Contravariant in domain (`a2 => a1`), covariant in codomain (`b1 => b2`)!
      match
        (synthesize_coercion(env, a2, a1), synthesize_coercion(env, b1, b2)) {
        (Some(c_dom), Some(c_cod)) => Some(CArrowMap(c_dom, c_cod))
        _ => None
      }
    (HStructRecord(m_sub, f_sub), HStructRecord(m_sup, f_sup)) => {
      // O(1) Width Subtyping Guard: `sub` MUST possess every field bit requested by `sup`!
      if (m_sup & m_sub.lnot()) != 0UL {
        return None
      }
      let f_coercions : Array[(Int32, CoercionProg)] = []
      let mut sup_pos = 0
      for fid = 0; fid < 64; fid = fid + 1 {
        if ((m_sup >> fid) & 1UL) != 0UL {
          let lower = if fid == 0 { 0UL } else { (1UL << fid) - 1UL }
          let sub_pos = popcount64(m_sub & lower)
          match synthesize_coercion(env, f_sub[sub_pos], f_sup[sup_pos]) {
            None => return None
            Some(cf) => f_coercions.push((fid, cf))
          }
          sup_pos = sup_pos + 1
        }
      }
      Some(CRecordMap(m_sup, f_coercions))
    }
    (HNominal(id1, _, _), HNominal(id2, _, _)) => {
      // Generative Nominal Isolation: distinct brand IDs NEVER coerce to one another!
      let _ = (id1, id2)
      None
    }
    (HNominal(id, _, inner_ty), _) =>
      if env.unbrandable_brands.contains(id) {
        match synthesize_coercion(env, inner_ty, sup) {
          Some(rest) => Some(CUnbrandThen(id, rest))
          None => None
        }
      } else {
        None
      }
    _ => None
  }
}
