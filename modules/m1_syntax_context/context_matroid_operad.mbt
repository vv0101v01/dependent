///|
/// Module M1 — Flat Telescope Contexts, Mirror Index/Level Duality,
/// Simplicial Degeneracy/Face Maps, Context Dependency Matroid,
/// Colored Operad Grafting, and Hash-Consing Syntax Arena.

///|
/// O(1) Mirror Duality: De Bruijn index i -> De Bruijn level l = depth - 1 - i.
pub fn idx_to_lvl(depth : Int32, idx : Int32) -> Int32 raise SyntaxError {
  if idx < 0 || idx >= depth {
    raise SyntaxError::InvalidDeBruijnIndex(idx)
  }
  depth - 1 - idx
}

///|
/// O(1) Mirror Duality: De Bruijn level l -> De Bruijn index i = depth - 1 - l.
pub fn lvl_to_idx(depth : Int32, lvl : Int32) -> Int32 raise SyntaxError {
  if lvl < 0 || lvl >= depth {
    raise SyntaxError::InvalidContextPosition(lvl)
  }
  depth - 1 - lvl
}

///|
#derive(Eq, Debug)
pub(all) struct CtxEntry {
  name : String
  ty : SynExpr
  local_def : SynExpr?
  direct_lvl_mask : UInt64
  trans_lvl_mask : UInt64
}

///|
pub extend CtxEntry with Eq::{equal, not_equal}

///|
pub extend CtxEntry with @debug.Debug::{to_repr}

///|
#derive(Eq, Debug)
pub(all) struct Context {
  entries : Array[CtxEntry]
}

///|
pub extend Context with Eq::{equal, not_equal}

///|
pub extend Context with @debug.Debug::{to_repr}

///|
pub fn Context::empty() -> Context {
  { entries: [], }
}

///|
pub fn Context::len(self : Context) -> Int32 {
  self.entries.length()
}

///|
/// Convert an expression's De Bruijn index occurrence mask (in context of length `depth`)
/// into a De Bruijn level bitmask for levels 0 .. min(depth, 64) - 1.
pub fn expr_level_mask_in_ctx(e : SynExpr, depth : Int32) -> UInt64 {
  if e.max_free == 0 || depth <= 0 {
    return 0UL
  }
  let mut lvl_mask : UInt64 = 0UL
  let limit = if depth < 64 { depth } else { 64 }
  for lvl = 0; lvl < limit; lvl = lvl + 1 {
    let idx = depth - 1 - lvl
    if e.has_free_var(idx) {
      lvl_mask = lvl_mask | (1UL << lvl)
    }
  }
  lvl_mask
}

///|
fn compute_trans_mask(entries : Array[CtxEntry], direct : UInt64) -> UInt64 {
  let mut acc = direct
  let n = entries.length()
  let limit = if n < 64 { n } else { 64 }
  for lvl = 0; lvl < limit; lvl = lvl + 1 {
    if (acc & (1UL << lvl)) != 0UL {
      acc = acc | entries[lvl].trans_lvl_mask
    }
  }
  acc
}

///|
/// Extend context `Γ` with `(name : ty)` where `ty` is scoped over `Γ` (`|Γ| = d`).
/// Incrementally computes exact transitive level dependency mask in O(|Γ|) bit operations.
pub fn Context::extend_var(
  self : Context,
  name : String,
  ty : SynExpr,
) -> Context {
  let d = self.entries.length()
  let direct = expr_level_mask_in_ctx(ty, d)
  let trans = compute_trans_mask(self.entries, direct)
  let next = self.entries.copy()
  next.push({
    name,
    ty,
    local_def: None,
    direct_lvl_mask: direct,
    trans_lvl_mask: trans,
  })
  { entries: next, }
}

///|
/// Extend context `Γ` with local let-binding `(name : ty := val)` (zeta-binders).
pub fn Context::extend_def(
  self : Context,
  name : String,
  ty : SynExpr,
  val : SynExpr,
) -> Context {
  let d = self.entries.length()
  let direct = expr_level_mask_in_ctx(ty, d) | expr_level_mask_in_ctx(val, d)
  let trans = compute_trans_mask(self.entries, direct)
  let next = self.entries.copy()
  next.push({
    name,
    ty,
    local_def: Some(val),
    direct_lvl_mask: direct,
    trans_lvl_mask: trans,
  })
  { entries: next, }
}

///|
/// O(1) lookup by De Bruijn index `idx`, returning the type shifted by `idx + 1`
/// so it is valid in the full context `Γ`.
pub fn Context::lookup_type_by_idx(
  self : Context,
  idx : Int32,
) -> SynExpr raise SyntaxError {
  let d = self.entries.length()
  let lvl = idx_to_lvl(d, idx)
  let entry = self.entries[lvl]
  shift_expr_simple(entry.ty, idx + 1, 0)
}

///|
/// O(1) lookup of raw context entry by De Bruijn level `lvl`.
pub fn Context::lookup_entry_by_lvl(
  self : Context,
  lvl : Int32,
) -> CtxEntry raise SyntaxError {
  if lvl < 0 || lvl >= self.entries.length() {
    raise SyntaxError::InvalidContextPosition(lvl)
  }
  self.entries[lvl]
}

///|
/// Exact dependency query: returns true iff hypothesis at `later_lvl` transitively
/// depends on hypothesis at `earlier_lvl`.
/// - Both levels < 64: exact O(1) 64-bit transitive-mask bit test.
/// - Otherwise: worklist sweep over direct dependencies (each resolved exactly via
///   `has_free_var`), short-circuiting through the exact 64-bit masks once the sweep
///   re-enters the mask window — the pre-64-bit masks stay exact for levels < 64.
fn ctx_entry_direct_dep(
  entries : Array[CtxEntry],
  later_lvl : Int32,
  target_lvl : Int32,
) -> Bool {
  let e = entries[later_lvl]
  let idx = later_lvl - 1 - target_lvl
  if e.ty.has_free_var(idx) {
    return true
  }
  match e.local_def {
    Some(v) => v.has_free_var(idx)
    None => false
  }
}

///|
pub fn Context::lvl_depends_on(
  self : Context,
  later_lvl : Int32,
  earlier_lvl : Int32,
) -> Bool {
  if earlier_lvl < 0 ||
    later_lvl <= earlier_lvl ||
    later_lvl >= self.entries.length() {
    return false
  }
  if later_lvl < 64 {
    return (self.entries[later_lvl].trans_lvl_mask & (1UL << earlier_lvl)) !=
      0UL
  }
  // Deep transitive sweep: dependencies only point strictly downwards, so any
  // dependency path from `later_lvl` down to `earlier_lvl` visits levels in
  // `[earlier_lvl, later_lvl)` in decreasing order.
  let worklist : Array[Int32] = [later_lvl]
  let visited : Map[Int32, Bool] = Map([])
  visited[later_lvl] = true
  let mut head = 0
  while head < worklist.length() {
    let l = worklist[head]
    head = head + 1
    if l < 64 {
      // Inside the mask window the stored transitive mask is EXACT for all levels < l.
      if (self.entries[l].trans_lvl_mask & (1UL << earlier_lvl)) != 0UL {
        return true
      }
      continue
    }
    let mut t = earlier_lvl
    while t < l {
      if ctx_entry_direct_dep(self.entries, l, t) {
        if t == earlier_lvl {
          return true
        }
        if t < 64 {
          // Exact O(1) shortcut through the stored transitive mask of `t`.
          if (self.entries[t].trans_lvl_mask & (1UL << earlier_lvl)) != 0UL {
            return true
          }
        } else if !visited.contains(t) {
          visited[t] = true
          worklist.push(t)
        }
      }
      t = t + 1
    }
  }
  false
}

///|
/// Simplicial Degeneracy Map σ_k(Γ, name, W):
/// Inserts a fresh hypothesis `(name : W)` at level `pos` (where `W` is valid in `Γ[0..pos)`),
/// shifting all downstream context types `Γ[pos..]` cleanly.
pub fn Context::simplicial_weaken_at(
  self : Context,
  pos : Int32,
  name : String,
  inserted_ty : SynExpr,
) -> Context raise SyntaxError {
  let n = self.entries.length()
  if pos < 0 || pos > n {
    raise SyntaxError::InvalidContextPosition(pos)
  }
  let mut out = Context::empty()
  for i = 0; i < pos; i = i + 1 {
    let e = self.entries[i]
    match e.local_def {
      None => out = out.extend_var(e.name, e.ty)
      Some(v) => out = out.extend_def(e.name, e.ty, v)
    }
  }
  out = out.extend_var(name, inserted_ty)
  for i = pos; i < n; i = i + 1 {
    let e = self.entries[i]
    let cutoff = i - pos
    let shifted_ty = shift_expr_simple(e.ty, 1, cutoff)
    match e.local_def {
      None => out = out.extend_var(e.name, shifted_ty)
      Some(v) => {
        let shifted_v = shift_expr_simple(v, 1, cutoff)
        out = out.extend_def(e.name, shifted_ty, shifted_v)
      }
    }
  }
  out
}

///|
/// Simplicial Face Map δ_k(Γ):
/// Strengthens (removes) hypothesis at level `pos` iff no downstream entry depends on `pos`.
/// Verified in O(n) using O(1) bitmask dependency checks per entry.
pub fn Context::simplicial_strengthen_at(
  self : Context,
  pos : Int32,
) -> Context raise SyntaxError {
  let n = self.entries.length()
  if pos < 0 || pos >= n {
    raise SyntaxError::InvalidContextPosition(pos)
  }
  for i = pos + 1; i < n; i = i + 1 {
    if self.lvl_depends_on(i, pos) {
      raise SyntaxError::StrengtheningBlocked(pos)
    }
  }
  let mut out = Context::empty()
  for i = 0; i < pos; i = i + 1 {
    let e = self.entries[i]
    match e.local_def {
      None => out = out.extend_var(e.name, e.ty)
      Some(v) => out = out.extend_def(e.name, e.ty, v)
    }
  }
  for i = pos + 1; i < n; i = i + 1 {
    let e = self.entries[i]
    let cutoff = i - 1 - pos
    let str_ty = try_strengthen_expr(e.ty, cutoff)
    match e.local_def {
      None => out = out.extend_var(e.name, str_ty)
      Some(v) => {
        let str_v = try_strengthen_expr(v, cutoff)
        out = out.extend_def(e.name, str_ty, str_v)
      }
    }
  }
  out
}

///|
/// Matroid Independence Check: returns true iff a subset of context levels `subset_mask`
/// forms an independent antichain (no element in the subset transitively depends on another).
/// Runs in O(popcount) bitmask intersections!
pub fn Context::is_matroid_independent_set(
  self : Context,
  subset_mask : UInt64,
) -> Bool {
  let n = self.entries.length()
  let limit = if n < 64 { n } else { 64 }
  for lvl = 0; lvl < limit; lvl = lvl + 1 {
    if (subset_mask & (1UL << lvl)) != 0UL {
      if (self.entries[lvl].trans_lvl_mask & subset_mask) != 0UL {
        return false
      }
    }
  }
  true
}

///|
/// Swap two adjacent independent hypotheses at `lvl` and `lvl + 1`, updating all De Bruijn indices
/// in `Γ` so typing validity is preserved (Exchange Admissibility Theorem for Independent Hypotheses).
pub fn Context::swap_adjacent_independent(
  self : Context,
  lvl : Int32,
) -> Context raise SyntaxError {
  let n = self.entries.length()
  if lvl < 0 || lvl + 1 >= n {
    raise SyntaxError::InvalidContextPosition(lvl)
  }
  if self.lvl_depends_on(lvl + 1, lvl) {
    raise SyntaxError::NonIndependentSwap(lvl, lvl + 1)
  }
  let e_a = self.entries[lvl]
  let e_b = self.entries[lvl + 1]
  // e_b.ty does NOT depend onVar(0) (= e_a), so strengthen cutoff 0 to move e_b before e_a:
  let b_ty_before = try_strengthen_expr(e_b.ty, 0)
  let b_def_before = match e_b.local_def {
    None => None
    Some(v) => Some(try_strengthen_expr(v, 0))
  }
  // e_a.ty moves 1 step later (under b), so weaken by +1 at cutoff 0:
  let a_ty_after = shift_expr_simple(e_a.ty, 1, 0)
  let a_def_after = match e_a.local_def {
    None => None
    Some(v) => Some(shift_expr_simple(v, 1, 0))
  }
  let mut out = Context::empty()
  for i = 0; i < lvl; i = i + 1 {
    let e = self.entries[i]
    match e.local_def {
      None => out = out.extend_var(e.name, e.ty)
      Some(v) => out = out.extend_def(e.name, e.ty, v)
    }
  }
  match b_def_before {
    None => out = out.extend_var(e_b.name, b_ty_before)
    Some(v) => out = out.extend_def(e_b.name, b_ty_before, v)
  }
  match a_def_after {
    None => out = out.extend_var(e_a.name, a_ty_after)
    Some(v) => out = out.extend_def(e_a.name, a_ty_after, v)
  }
  // For entries at i >= lvl + 2, swap De Bruijn indices corresponding to lvl and lvl+1:
  for i = lvl + 2; i < n; i = i + 1 {
    let e = self.entries[i]
    let idx_b_old = i - 1 - (lvl + 1)
    let swap_sub = build_adjacent_swap_subst(idx_b_old)
    let swapped_ty = apply_subst(e.ty, swap_sub)
    match e.local_def {
      None => out = out.extend_var(e.name, swapped_ty)
      Some(v) =>
        out = out.extend_def(e.name, swapped_ty, apply_subst(v, swap_sub))
    }
  }
  out
}

///|
fn build_adjacent_swap_subst(idx_low : Int32) -> Subst {
  // Swaps Var(idx_low) and Var(idx_low + 1), leaving all other variables unchanged.
  let base = Cons(
    mk_var_unchecked(1),
    Cons(mk_var_unchecked(0), subst_shift(2)),
  )
  subst_lift(idx_low, base)
}

///|
/// Compute minimal transitive dependency bitmask of context levels required by `expr` in `self`.
pub fn Context::minimal_support_mask(self : Context, expr : SynExpr) -> UInt64 {
  let d = self.entries.length()
  let direct = expr_level_mask_in_ctx(expr, d)
  compute_trans_mask(self.entries, direct)
}

///|
/// Colored Operad Simultaneous Grafting:
/// Replaces every `Hole(slot)` in `host` with `plugs[slot]`, automatically shifting free variables
/// in `plugs[slot]` by the exact binder depth accumulated from the root of `host` to that hole!
/// If `host.slot_mask == 0`, returns `host` in O(1) without traversal!
pub fn operad_graft(
  host : SynExpr,
  plugs : Array[(Int32, SynExpr)],
) -> SynExpr raise SyntaxError {
  if host.slot_mask == 0UL {
    return host
  }
  operad_graft_rec(host, plugs, 0)
}

///|
fn find_plug(
  plugs : Array[(Int32, SynExpr)],
  slot : Int32,
) -> SynExpr raise SyntaxError {
  for pair in plugs {
    let (s, expr) = pair
    if s == slot {
      return expr
    }
  }
  raise SyntaxError::UnboundOperadSlot(slot)
}

///|
fn operad_graft_rec(
  e : SynExpr,
  plugs : Array[(Int32, SynExpr)],
  binder_depth : Int32,
) -> SynExpr raise SyntaxError {
  if e.slot_mask == 0UL {
    return e
  }
  match e.kind {
    Hole(s) => {
      let plugged = find_plug(plugs, s)
      shift_expr_simple(plugged, binder_depth, 0)
    }
    Var(_)
    | Univ(_)
    | PolyUniv(_, _)
    | PropSort
    | UnitTy
    | UnitVal
    | EmptyTy
    | NatTy
    | Zero
    | BoolTy
    | BoolLit(_)
    | ConstRef(_, _) => e
    SmallEncode(l, a) =>
      mk_small_encode(l, operad_graft_rec(a, plugs, binder_depth))
    SmallDecode(l, a) =>
      mk_small_decode(l, operad_graft_rec(a, plugs, binder_depth))
    Pi(n, a, b) =>
      mk_pi(
        n,
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth + 1),
      )
    Lam(n, a, b) =>
      mk_lam(
        n,
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth + 1),
      )
    App(a, b) =>
      mk_app(
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth),
      )
    Sigma(n, a, b) =>
      mk_sigma(
        n,
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth + 1),
      )
    Pair(a, b, c) =>
      mk_pair(
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth),
        operad_graft_rec(c, plugs, binder_depth + 1),
      )
    Fst(a) => mk_fst(operad_graft_rec(a, plugs, binder_depth))
    Snd(a) => mk_snd(operad_graft_rec(a, plugs, binder_depth))
    Absurd(a, b) =>
      mk_absurd(
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth),
      )
    SumTy(a, b) =>
      mk_sum_ty(
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth),
      )
    Inl(a, b) =>
      mk_inl(
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth),
      )
    Inr(a, b) =>
      mk_inr(
        operad_graft_rec(a, plugs, binder_depth),
        operad_graft_rec(b, plugs, binder_depth),
      )
    CaseSum(sc, m, l, r) =>
      mk_case_sum(
        operad_graft_rec(sc, plugs, binder_depth),
        operad_graft_rec(m, plugs, binder_depth + 1),
        operad_graft_rec(l, plugs, binder_depth + 1),
        operad_graft_rec(r, plugs, binder_depth + 1),
      )
    Succ(a) => mk_succ(operad_graft_rec(a, plugs, binder_depth))
    NatRec(m, z, st, tg) =>
      mk_nat_rec(
        operad_graft_rec(m, plugs, binder_depth + 1),
        operad_graft_rec(z, plugs, binder_depth),
        operad_graft_rec(st, plugs, binder_depth + 2),
        operad_graft_rec(tg, plugs, binder_depth),
      )
    IdTy(t, l, r) =>
      mk_id_ty(
        operad_graft_rec(t, plugs, binder_depth),
        operad_graft_rec(l, plugs, binder_depth),
        operad_graft_rec(r, plugs, binder_depth),
      )
    Refl(t, x) =>
      mk_refl(
        operad_graft_rec(t, plugs, binder_depth),
        operad_graft_rec(x, plugs, binder_depth),
      )
    JElim(t, l, m, rf, r, eqp) =>
      mk_j_elim(
        operad_graft_rec(t, plugs, binder_depth),
        operad_graft_rec(l, plugs, binder_depth),
        operad_graft_rec(m, plugs, binder_depth + 2),
        operad_graft_rec(rf, plugs, binder_depth),
        operad_graft_rec(r, plugs, binder_depth),
        operad_graft_rec(eqp, plugs, binder_depth),
      )
    SquashTy(a) => mk_squash_ty(operad_graft_rec(a, plugs, binder_depth))
    SquashIntro(a) => mk_squash_intro(operad_graft_rec(a, plugs, binder_depth))
  }
}

///|
/// Hash-Consed Syntax Arena: maps structurally identical `SynExpr` trees to canonical
/// `Int32` intern IDs so structural equality reduces to O(1) integer comparison.
pub(all) struct SyntaxArena {
  nodes : Array[SynExpr]
  buckets : Map[UInt64, Array[Int32]]
}

///|
pub fn SyntaxArena::new() -> SyntaxArena {
  { nodes: [], buckets: {}, }
}

///|
pub fn SyntaxArena::intern(self : SyntaxArena, e : SynExpr) -> Int32 {
  match self.buckets.get(e.hash64) {
    Some(ids) => {
      for id in ids {
        if self.nodes[id] == e {
          return id
        }
      }
      let new_id = self.nodes.length()
      self.nodes.push(e)
      ids.push(new_id)
      new_id
    }
    None => {
      let new_id = self.nodes.length()
      self.nodes.push(e)
      self.buckets[e.hash64] = [new_id]
      new_id
    }
  }
}

///|
pub fn SyntaxArena::get_node(self : SyntaxArena, id : Int32) -> SynExpr {
  self.nodes[id]
}

///|
pub fn SyntaxArena::size(self : SyntaxArena) -> Int32 {
  self.nodes.length()
}
