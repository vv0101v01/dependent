///|
/// Module M4 — Gentzen Sequent Calculus LJD with Hauptsatz Cut-Elimination,
/// Commuting Diagram Verification (Cut-Elimination == β-Normalization),
/// Classical-to-Intuitionistic CPS Negative Translation, and Certified Proof Erasure.

///|
/// Gentzen Intuitionistic Sequent Derivations `Γ ⊢ C`
/// where antecedent `Γ` is indexed by De Bruijn indices `0` (top/most recent) .. `|Γ|-1`.
#derive(Eq, Debug)
pub(all) enum SequentProof {
  SInit(Int32, PropFormula)
  STopR
  SBotL(Int32, PropFormula)
  SConjR(SequentProof, SequentProof)
  SConjL1(Int32, PropFormula, PropFormula, SequentProof)
  SConjL2(Int32, PropFormula, PropFormula, SequentProof)
  SDisjR1(PropFormula, SequentProof)
  SDisjR2(PropFormula, SequentProof)
  SDisjL(Int32, PropFormula, PropFormula, SequentProof, SequentProof)
  SImplR(PropFormula, SequentProof)
  SImplL(Int32, PropFormula, PropFormula, SequentProof, SequentProof)
  SCut(PropFormula, SequentProof, SequentProof)
}

///|
pub extend SequentProof with Eq::{equal, not_equal}

///|
pub extend SequentProof with @debug.Debug::{to_repr}

///|
/// Count the number of `SCut` inferences remaining in a sequent derivation.
pub fn count_cuts(p : SequentProof) -> Int32 {
  match p {
    SInit(_, _) | STopR | SBotL(_, _) => 0
    SConjR(a, b) | SDisjL(_, _, _, a, b) | SImplL(_, _, _, a, b) =>
      count_cuts(a) + count_cuts(b)
    SConjL1(_, _, _, a)
    | SConjL2(_, _, _, a)
    | SDisjR1(_, a)
    | SDisjR2(_, a)
    | SImplR(_, a) => count_cuts(a)
    SCut(_, a, b) => 1 + count_cuts(a) + count_cuts(b)
  }
}

///|
/// Shift antecedent De Bruijn indices >= `cutoff` in `SequentProof` by `delta` (Structural Weakening Lemma!).
pub fn weaken_sequent(
  p : SequentProof,
  delta : Int32,
  cutoff : Int32,
) -> SequentProof {
  if delta == 0 {
    return p
  }
  match p {
    SInit(i, f) => SInit(if i >= cutoff { i + delta } else { i }, f)
    STopR => STopR
    SBotL(i, c) => SBotL(if i >= cutoff { i + delta } else { i }, c)
    SConjR(a, b) =>
      SConjR(weaken_sequent(a, delta, cutoff), weaken_sequent(b, delta, cutoff))
    SConjL1(i, a, b, sub) =>
      SConjL1(
        if i >= cutoff {
          i + delta
        } else {
          i
        },
        a,
        b,
        weaken_sequent(sub, delta, cutoff + 1),
      )
    SConjL2(i, a, b, sub) =>
      SConjL2(
        if i >= cutoff {
          i + delta
        } else {
          i
        },
        a,
        b,
        weaken_sequent(sub, delta, cutoff + 1),
      )
    SDisjR1(r, sub) => SDisjR1(r, weaken_sequent(sub, delta, cutoff))
    SDisjR2(l, sub) => SDisjR2(l, weaken_sequent(sub, delta, cutoff))
    SDisjL(i, a, b, lsub, rsub) =>
      SDisjL(
        if i >= cutoff {
          i + delta
        } else {
          i
        },
        a,
        b,
        weaken_sequent(lsub, delta, cutoff + 1),
        weaken_sequent(rsub, delta, cutoff + 1),
      )
    SImplR(dom, sub) => SImplR(dom, weaken_sequent(sub, delta, cutoff + 1))
    SImplL(i, a, b, arg_p, cont_p) =>
      SImplL(
        if i >= cutoff {
          i + delta
        } else {
          i
        },
        a,
        b,
        weaken_sequent(arg_p, delta, cutoff),
        weaken_sequent(cont_p, delta, cutoff + 1),
      )
    SCut(cf, d1, d2) =>
      SCut(
        cf,
        weaken_sequent(d1, delta, cutoff),
        weaken_sequent(d2, delta, cutoff + 1),
      )
  }
}

///|
/// Translate Gentzen Sequent Proof `Γ ⊢ C` directly into a Curry-Howard `CHTerm`!
/// Notice `SCut(A, d1, d2)` compiles into the β-detour `(λx:⟦A⟧. ⟦d2⟧) ⟦d1⟧`!
pub fn sequent_to_ch_term(p : SequentProof) -> CHTerm {
  match p {
    SInit(i, _) => PTVar(i)
    STopR => PTUnit
    SBotL(i, c) => PTAbsurd(formula_to_ch_type(c), PTVar(i))
    SConjR(a, b) => PTPair(sequent_to_ch_term(a), sequent_to_ch_term(b))
    SConjL1(i, _, _, sub) =>
      subst_ch_term(sequent_to_ch_term(sub), 0, PTFst(PTVar(i)))
    SConjL2(i, _, _, sub) =>
      subst_ch_term(sequent_to_ch_term(sub), 0, PTSnd(PTVar(i)))
    SDisjR1(r, sub) => PTInl(formula_to_ch_type(r), sequent_to_ch_term(sub))
    SDisjR2(l, sub) => PTInr(formula_to_ch_type(l), sequent_to_ch_term(sub))
    SDisjL(i, _, _, lsub, rsub) =>
      PTCase(PTVar(i), sequent_to_ch_term(lsub), sequent_to_ch_term(rsub))
    SImplR(dom, sub) => PTLam(formula_to_ch_type(dom), sequent_to_ch_term(sub))
    SImplL(i, _, _, arg_p, cont_p) => {
      let app_tm = PTApp(PTVar(i), sequent_to_ch_term(arg_p))
      subst_ch_term(sequent_to_ch_term(cont_p), 0, app_tm)
    }
    SCut(cut_f, d1, d2) =>
      PTApp(
        PTLam(formula_to_ch_type(cut_f), sequent_to_ch_term(d2)),
        sequent_to_ch_term(d1),
      )
  }
}

///|
/// Local Axiom (Gentzen's Hauptsatz — Constructive Cut-Elimination Algorithm):
/// Eliminates ALL `SCut` rules from `p`, returning a strictly cut-free `SequentProof` (`count_cuts == 0`)!
pub fn eliminate_cuts(p : SequentProof) -> SequentProof raise LogicError {
  match p {
    SInit(_, _) | STopR | SBotL(_, _) => p
    SConjR(a, b) => SConjR(eliminate_cuts(a), eliminate_cuts(b))
    SConjL1(i, a, b, s) => SConjL1(i, a, b, eliminate_cuts(s))
    SConjL2(i, a, b, s) => SConjL2(i, a, b, eliminate_cuts(s))
    SDisjR1(r, s) => SDisjR1(r, eliminate_cuts(s))
    SDisjR2(l, s) => SDisjR2(l, eliminate_cuts(s))
    SDisjL(i, a, b, l, r) =>
      SDisjL(i, a, b, eliminate_cuts(l), eliminate_cuts(r))
    SImplR(dom, s) => SImplR(dom, eliminate_cuts(s))
    SImplL(i, a, b, arg_p, cont_p) =>
      SImplL(i, a, b, eliminate_cuts(arg_p), eliminate_cuts(cont_p))
    SCut(cut_f, d1, d2) => {
      let cf1 = eliminate_cuts(d1)
      let cf2 = eliminate_cuts(d2)
      admissible_cut(cut_f, cf1, cf2, 0)
    }
  }
}

///|
/// Admissible Cut `Γ_front (length k), A_k, Γ_back` substituted with cut-free `d1` (valid in `Γ_back` shifted by `k`):
/// Performs Principal Cut Reductions, Axiom/Bot Reductions, and Left/Right Commutative Reductions!
fn admissible_cut(
  cut_f : PropFormula,
  d1 : SequentProof,
  d2 : SequentProof,
  idx : Int32,
) -> SequentProof raise LogicError {
  // First handle Left Commutative / Axiom / Bot reductions on `d1` when `d1` is NOT a right-intro!
  match d1 {
    SBotL(bi, _) => return infer_bot_conclusion(bi, d2, idx)
    SConjL1(li, a, b, sub1) =>
      return SConjL1(
        li,
        a,
        b,
        admissible_cut(cut_f, sub1, weaken_sequent(d2, 1, idx + 1), idx),
      )
    SConjL2(li, a, b, sub1) =>
      return SConjL2(
        li,
        a,
        b,
        admissible_cut(cut_f, sub1, weaken_sequent(d2, 1, idx + 1), idx),
      )
    SDisjL(li, a, b, ls1, rs1) => {
      let d2_w = weaken_sequent(d2, 1, idx + 1)
      return SDisjL(
        li,
        a,
        b,
        admissible_cut(cut_f, ls1, d2_w, idx),
        admissible_cut(cut_f, rs1, d2_w, idx),
      )
    }
    SImplL(li, a, b, arg1, cont1) => {
      let d2_w = weaken_sequent(d2, 1, idx + 1)
      return SImplL(li, a, b, arg1, admissible_cut(cut_f, cont1, d2_w, idx))
    }
    _ => ()
  }

  // Now recurse structurally on `d2` (Right Commutative, Axiom, and Principal Cut Reductions):
  match d2 {
    SInit(i, f) =>
      if i == idx {
        d1
      } else if i > idx {
        SInit(i - 1, f)
      } else {
        SInit(i, f)
      }
    STopR => STopR
    SBotL(i, c) =>
      if i == idx {
        // Cut formula is FBot, and `d1` (not SBotL) must be SInit(j, FBot):
        match d1 {
          SInit(j, _) => SBotL(j, c)
          _ =>
            raise LogicError::InvalidSequentRule(
              "Closed proof of FBot impossible",
            )
        }
      } else if i > idx {
        SBotL(i - 1, c)
      } else {
        SBotL(i, c)
      }
    SConjR(l2, r2) =>
      SConjR(
        admissible_cut(cut_f, d1, l2, idx),
        admissible_cut(cut_f, d1, r2, idx),
      )
    SDisjR1(r_form, sub2) =>
      SDisjR1(r_form, admissible_cut(cut_f, d1, sub2, idx))
    SDisjR2(l_form, sub2) =>
      SDisjR2(l_form, admissible_cut(cut_f, d1, sub2, idx))
    SImplR(dom, sub2) =>
      SImplR(
        dom,
        admissible_cut(cut_f, weaken_sequent(d1, 1, 0), sub2, idx + 1),
      )
    SConjL1(i, a, b, sub2) => {
      let sub_after = admissible_cut(
        cut_f,
        weaken_sequent(d1, 1, 0),
        sub2,
        idx + 1,
      )
      if i == idx {
        // Principal Conjunction-1 Cut!
        match d1 {
          SConjR(d1_a, _) => admissible_cut(a, d1_a, sub_after, 0)
          SInit(j, _) => SConjL1(j, a, b, sub_after)
          _ => raise LogicError::InvalidSequentRule("ConjL1 principal mismatch")
        }
      } else {
        let adj_i = if i > idx { i - 1 } else { i }
        SConjL1(adj_i, a, b, sub_after)
      }
    }
    SConjL2(i, a, b, sub2) => {
      let sub_after = admissible_cut(
        cut_f,
        weaken_sequent(d1, 1, 0),
        sub2,
        idx + 1,
      )
      if i == idx {
        match d1 {
          SConjR(_, d1_b) => admissible_cut(b, d1_b, sub_after, 0)
          SInit(j, _) => SConjL2(j, a, b, sub_after)
          _ => raise LogicError::InvalidSequentRule("ConjL2 principal mismatch")
        }
      } else {
        let adj_i = if i > idx { i - 1 } else { i }
        SConjL2(adj_i, a, b, sub_after)
      }
    }
    SDisjL(i, a, b, l2, r2) => {
      let d1_w = weaken_sequent(d1, 1, 0)
      let l_after = admissible_cut(cut_f, d1_w, l2, idx + 1)
      let r_after = admissible_cut(cut_f, d1_w, r2, idx + 1)
      if i == idx {
        match d1 {
          SDisjR1(_, d1_a) => admissible_cut(a, d1_a, l_after, 0)
          SDisjR2(_, d1_b) => admissible_cut(b, d1_b, r_after, 0)
          SInit(j, _) => SDisjL(j, a, b, l_after, r_after)
          _ => raise LogicError::InvalidSequentRule("DisjL principal mismatch")
        }
      } else {
        let adj_i = if i > idx { i - 1 } else { i }
        SDisjL(adj_i, a, b, l_after, r_after)
      }
    }
    SImplL(i, a, b, arg2, cont2) => {
      let arg_after = admissible_cut(cut_f, d1, arg2, idx)
      let cont_after = admissible_cut(
        cut_f,
        weaken_sequent(d1, 1, 0),
        cont2,
        idx + 1,
      )
      if i == idx {
        // Principal Implication Cut: `d1 = SImplR(a, body1)` cut with `arg_after : a` and `cont_after : b -> C`!
        match d1 {
          SImplR(_, body1) => {
            let b_proof = admissible_cut(a, arg_after, body1, 0)
            admissible_cut(b, b_proof, cont_after, 0)
          }
          SInit(j, _) => SImplL(j, a, b, arg_after, cont_after)
          _ => raise LogicError::InvalidSequentRule("ImplL principal mismatch")
        }
      } else {
        let adj_i = if i > idx { i - 1 } else { i }
        SImplL(adj_i, a, b, arg_after, cont_after)
      }
    }
    SCut(inner_f, c1, c2) => {
      let c1_cf = eliminate_cuts(c1)
      let c2_cf = eliminate_cuts(c2)
      let merged = admissible_cut(inner_f, c1_cf, c2_cf, 0)
      admissible_cut(cut_f, d1, merged, idx)
    }
  }
}

///|
fn infer_bot_conclusion(
  bot_idx_in_d1 : Int32,
  d2 : SequentProof,
  cut_idx : Int32,
) -> SequentProof {
  // Adjust `bot_idx_in_d1`: in `d2` after removing `cut_idx`, `d1` had `cut_idx` items in front of it:
  let final_bot_idx = bot_idx_in_d1 + cut_idx
  SBotL(final_bot_idx, extract_sequent_conclusion(d2))
}

///|
fn extract_sequent_conclusion(p : SequentProof) -> PropFormula {
  match p {
    SInit(_, f) => f
    STopR => FTop
    SBotL(_, c) => c
    SConjR(a, b) =>
      FConj(extract_sequent_conclusion(a), extract_sequent_conclusion(b))
    SConjL1(_, _, _, s) | SConjL2(_, _, _, s) => extract_sequent_conclusion(s)
    SDisjR1(r, s) => FDisj(extract_sequent_conclusion(s), r)
    SDisjR2(l, s) => FDisj(l, extract_sequent_conclusion(s))
    SDisjL(_, _, _, l, _) => extract_sequent_conclusion(l)
    SImplR(dom, s) => FImpl(dom, extract_sequent_conclusion(s))
    SImplL(_, _, _, _, cont) => extract_sequent_conclusion(cont)
    SCut(_, _, d2) => extract_sequent_conclusion(d2)
  }
}

///|
/// Plotkin / Gödel-Gentzen / Kuroda Continuation-Passing (Double-Negation) Translation
/// into answer proposition `ans`: `¬_R X := X -> R`, `¬¬_R X := (X -> R) -> R`.
pub fn cps_neg(t : CHType, ans : CHType) -> CHType {
  TArrow(t, ans)
}

///|
pub fn cps_dneg(t : CHType, ans : CHType) -> CHType {
  TArrow(TArrow(t, ans), ans)
}

///|
/// Call-by-name CPS Formula Translation `⟦φ⟧_CPS^R`: embeds classical logic into constructive logic!
pub fn cps_translate_formula(f : PropFormula, ans : CHType) -> CHType {
  match f {
    FTop => cps_dneg(TUnit, ans)
    FBot => ans
    FAtom(p, args) => cps_dneg(TPredFamily(p, args.copy()), ans)
    FEq(s, l, r) => cps_dneg(TId(s, l, r), ans)
    FConj(a, b) =>
      cps_dneg(
        TProd(cps_translate_formula(a, ans), cps_translate_formula(b, ans)),
        ans,
      )
    FDisj(a, b) =>
      cps_dneg(
        TSum(cps_translate_formula(a, ans), cps_translate_formula(b, ans)),
        ans,
      )
    FImpl(a, b) =>
      cps_dneg(
        TArrow(cps_translate_formula(a, ans), cps_translate_formula(b, ans)),
        ans,
      )
    FForall(x, d, body) =>
      cps_dneg(TPi(x, d, cps_translate_formula(body, ans)), ans)
    FExists(x, d, body) =>
      cps_dneg(TSigma(x, d, cps_translate_formula(body, ans)), ans)
    FSquash(a) => cps_dneg(TSquash(cps_translate_formula(a, ans)), ans)
  }
}

///|
/// Synthesize constructive proof term for Double-Negated Law of Excluded Middle:
/// `⊢ ¬¬(P ∨ ¬P)` = `((P + (P -> ⊥)) -> ⊥) -> ⊥`
/// Proof term: `λk : (P + (P -> ⊥)) -> ⊥.  k (inr (λp : P. k (inl p)))`!
pub fn synthesize_dn_excluded_middle(p_ty : CHType) -> CHTerm {
  let not_p = TArrow(p_ty, TEmpty)
  let p_or_not_p = TSum(p_ty, not_p)
  let k_ty = TArrow(p_or_not_p, TEmpty)
  // Inside λk: k is #0. Inside λp: k is #1, p is #0.
  let inner_fn = PTLam(p_ty, PTApp(PTVar(1), PTInl(not_p, PTVar(0))))
  PTLam(k_ty, PTApp(PTVar(0), PTInr(p_ty, inner_fn)))
}

///|
/// Synthesize constructive CPS proof term for Classical Peirce's Law over continuation space `DNeg_R`:
/// Inhabits `(((P -> R) -> R -> ((Q -> R) -> R)) -> (P -> R) -> R) -> (P -> R) -> R`
/// Directly proves `((((P -> Q_R) -> P) -> P)` where `P = (A -> R) -> R`, `Q_R = R`:
/// More generally, for any `A` and answer `R`, `(((A -> (B -> R) -> R) -> A) -> A)` holds in CPS:
/// Here we construct the canonical Continuation Call/CC Witness of `(((A -> B) -> A) -> A)` in `DNeg_R`:
/// Type: `((((A -> B) -> A) -> A) -> R) -> R` when `B = R` (or `A -> B` via abort continuation `λa:A. abort_B (k_a a)`!).
pub fn synthesize_cps_peirce(a_ty : CHType, b_ty : CHType) -> CHTerm {
  // Proves `¬¬(((A -> B) -> A) -> A)` constructively for ANY types `A, B`!
  // Let Peirce = ((A -> B) -> A) -> A. We inhabit `(Peirce -> ⊥) -> ⊥`:
  // λk : Peirce -> ⊥.
  //   k (λh : (A -> B) -> A.
  //        h (λa : A. absurd_B (k (λ_ : (A -> B) -> A. a))))
  let a_to_b = TArrow(a_ty, b_ty)
  let h_ty = TArrow(a_to_b, a_ty)
  let peirce_ty = TArrow(h_ty, a_ty)
  let k_ty = TArrow(peirce_ty, TEmpty)
  // Inside λk (#0) -> λh (#0, k=#1) -> λa (#0, h=#1, k=#2) -> λ_ (#0, a=#1, h=#2, k=#3):
  let const_a = PTLam(h_ty, PTVar(1))
  let abort_b = PTAbsurd(b_ty, PTApp(PTVar(2), const_a))
  let fake_ab = PTLam(a_ty, abort_b)
  let peirce_fn = PTLam(h_ty, PTApp(PTVar(0), fake_ab))
  PTLam(k_ty, PTApp(PTVar(0), peirce_fn))
}

///|
/// Certified Proof-Erased Computational Lambda Term (Sozeau et al. 2025 Certified Erasure):
/// Strips all proof-irrelevant propositions (`TUnit`, `TId`, `TSquash`) down to `ErasedProp` (`□`).
#derive(Eq, Debug)
pub(all) enum ExtractedProg {
  EPVar(Int32)
  EPObj(ObjTerm)
  EPErasedProp
  EPPair(ExtractedProg, ExtractedProg)
  EPFst(ExtractedProg)
  EPSnd(ExtractedProg)
  EPInl(ExtractedProg)
  EPInr(ExtractedProg)
  EPCase(ExtractedProg, ExtractedProg, ExtractedProg)
  EPLam(ExtractedProg)
  EPApp(ExtractedProg, ExtractedProg)
}

///|
pub extend ExtractedProg with Eq::{equal, not_equal}

///|
pub extend ExtractedProg with @debug.Debug::{to_repr}

///|
/// Certified Erasure & Constructive Witness Extraction:
/// Given a well-typed proof `tm` in `prf_ctx`, erases all proof-irrelevant subterms to `EPErasedProp`
/// and extracts the pure computational witness for `TSigma` (`∃x:D. P(x)`) and `TPi` (`∀x:D. ...`)!
pub fn extract_computational_program(
  prf_ctx : Array[CHType],
  tm : CHTerm,
) -> ExtractedProg raise LogicError {
  let ty = infer_ch_term(prf_ctx, tm)
  if is_prop_irrelevant(ty) {
    return EPErasedProp
  }
  match tm {
    PTVar(i) => EPVar(i)
    PTUnit | PTRefl(_, _) | PTSquashBox(_) => EPErasedProp
    PTAbsurd(_, _) => EPErasedProp
    PTPair(a, b) => {
      let ea = extract_computational_program(prf_ctx, a)
      let eb = extract_computational_program(prf_ctx, b)
      match (ea, eb) {
        (ea_keep, EPErasedProp) => ea_keep
        (EPErasedProp, eb_keep) => eb_keep
        _ => EPPair(ea, eb)
      }
    }
    PTFst(p) => {
      let p_ty = infer_ch_term(prf_ctx, p)
      let ep = extract_computational_program(prf_ctx, p)
      match p_ty {
        TProd(_, b_ty) => if is_prop_irrelevant(b_ty) { ep } else { EPFst(ep) }
        _ => EPFst(ep)
      }
    }
    PTSnd(p) => {
      let p_ty = infer_ch_term(prf_ctx, p)
      let ep = extract_computational_program(prf_ctx, p)
      match p_ty {
        TProd(a_ty, _) => if is_prop_irrelevant(a_ty) { ep } else { EPSnd(ep) }
        _ => EPSnd(ep)
      }
    }
    PTInl(_, a) => EPInl(extract_computational_program(prf_ctx, a))
    PTInr(_, b) => EPInr(extract_computational_program(prf_ctx, b))
    PTCase(s, l, r) =>
      match infer_ch_term(prf_ctx, s) {
        TSum(lty, rty) => {
          let ctx_l = prf_ctx.copy()
          ctx_l.push(lty)
          let ctx_r = prf_ctx.copy()
          ctx_r.push(rty)
          EPCase(
            extract_computational_program(prf_ctx, s),
            extract_computational_program(ctx_l, l),
            extract_computational_program(ctx_r, r),
          )
        }
        other => raise LogicError::ExpectedSumProof(other)
      }
    PTLam(dom, body) => {
      let ext = prf_ctx.copy()
      ext.push(dom)
      EPLam(extract_computational_program(ext, body))
    }
    PTApp(f, a) =>
      EPApp(
        extract_computational_program(prf_ctx, f),
        extract_computational_program(prf_ctx, a),
      )
    PTDepLam(_, body) => {
      let shifted_ctx : Array[CHType] = []
      for t in prf_ctx {
        shifted_ctx.push(shift_ch_type_obj(t, 1, 0))
      }
      EPLam(extract_computational_program(shifted_ctx, body))
    }
    PTDepApp(f, o) => EPApp(extract_computational_program(prf_ctx, f), EPObj(o))
    PTPack(w, prf, _) => {
      let e_prf = extract_computational_program(prf_ctx, prf)
      match e_prf {
        // When the predicate body `P(x)` is proof-irrelevant (e.g. FEq or FSquash),
        // the existential package `<w, prf>` erases cleanly to JUST the pure witness `EPObj(w)`!
        EPErasedProp => EPObj(w)
        other => EPPair(EPObj(w), other)
      }
    }
    PTUnpack(ex, body) =>
      match infer_ch_term(prf_ctx, ex) {
        TSigma(_, _, fam_ty) => {
          let shifted_ctx : Array[CHType] = []
          for t in prf_ctx {
            shifted_ctx.push(shift_ch_type_obj(t, 1, 0))
          }
          shifted_ctx.push(fam_ty)
          EPApp(
            EPLam(extract_computational_program(shifted_ctx, body)),
            extract_computational_program(prf_ctx, ex),
          )
        }
        other => raise LogicError::ExpectedExistsProof(other)
      }
    PTLetSquash(_, _) => EPErasedProp
  }
}
