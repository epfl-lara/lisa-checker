import Lisa.Orthologic.Lowering
import Lisa.Orthologic.Provability

/-! Soundness of recognizing logical symbols and expanding them into conjunction,
negation and universal quantification. All equivalences are Ordered derivations. -/

namespace Lisa.Orthologic
open Expr Derivation Ordered

namespace Derivation
noncomputable section

theorem or_dual (hp : isFormula p) (hq : isFormula q) :
    ContextEq prop (or p q) (neg (and (neg p) (neg q))) := by
  have hnp := isFormula_neg hp
  have hnq := isFormula_neg hq
  have ha := isFormula_and hnp hnq
  have ho := isFormula_or hp hq
  have forward := or_le hp hq (isFormula_neg ha)
    (trans hp (isFormula_neg hnp) (isFormula_neg ha) (doubleNegIntro hp)
      (neg_mono ha hnp (and_left hnp hnq)))
    (trans hq (isFormula_neg hnq) (isFormula_neg ha) (doubleNegIntro hq)
      (neg_mono ha hnq (and_right hnp hnq)))
  have backward := le_and (isFormula_neg ho) hnp hnq
    (neg_mono hp ho (or_left hp hq)) (neg_mono hq ho (or_right hp hq))
  exact ContextEq.of_formula ho (isFormula_neg ha) ⟨forward⟩
    ⟨trans (isFormula_neg ha) (isFormula_neg (isFormula_neg ho)) ho
      (neg_mono (isFormula_neg ho) ha backward) (doubleNegElim ho)⟩

theorem imp_dual (hp : isFormula p) (hq : isFormula q) :
    ContextEq prop (imp p q) (neg (and p (neg q))) := by
  have hi := isFormula_imp hp hq
  have hnq := isFormula_neg hq
  have ha := isFormula_and hp hnq
  have hn := isFormula_neg ha
  have mp : AlphaBetaEtaProof (insert (imp p q) {p}) {q} := by
    simpa using ProofTree.leftImp (Γ := {p}) (Δ := ∅) (Ω := ∅) (Ξ := {q}) p q
      (singleton_sorted hp) isFSet_empty isFSet_empty (singleton_sorted hq) hp hq
      (.hypothesis p hp) (.hypothesis q hq)
  have dn := ProofTree.leftNot (Δ := ∅) q (isFSet_insert hi (singleton_sorted hp))
    isFSet_empty hq mp
  have da : AlphaBetaEtaProof (insert (and p (neg q)) {imp p q}) ∅ := by
    apply ProofTree.leftAnd p (neg q) (singleton_sorted hi) isFSet_empty hp hnq
    convert dn using 1
    ext e
    simp [or_comm, or_assoc]
  have forward : Entails (imp p q) (neg (and p (neg q))) :=
    .rightNot (Δ := ∅) _ (singleton_sorted hi) isFSet_empty ha da
  have excluded : AlphaBetaEtaProof ∅ (insert (neg q) {q}) :=
    .rightNot (Γ := ∅) q isFSet_empty (singleton_sorted hq) hq (.hypothesis q hq)
  have da' : AlphaBetaEtaProof {p} (insert (and p (neg q)) {q}) := by
    simpa using ProofTree.rightAnd (Γ := {p}) (Ω := ∅) (Δ := ∅) (Ξ := {q}) p (neg q)
      (singleton_sorted hp) isFSet_empty isFSet_empty (singleton_sorted hq) hp hnq
      (.hypothesis p hp) excluded
  have dn' := ProofTree.leftNot (and p (neg q)) (singleton_sorted hp) (singleton_sorted hq) ha da'
  have backward : Entails (neg (and p (neg q))) (imp p q) := by
    apply ProofTree.rightImp (Δ := ∅) p q (singleton_sorted hn) isFSet_empty hp hq
    convert dn' using 1
    ext e
    simp [or_comm]
  exact ContextEq.of_formula hi hn ⟨forward⟩ ⟨backward⟩

theorem iff_and (hp : isFormula p) (hq : isFormula q) :
    ContextEq prop (iff p q) (and (imp p q) (imp q p)) := by
  have hpq := isFormula_imp hp hq
  have hqp := isFormula_imp hq hp
  have ha := isFormula_and hpq hqp
  have forward : Entails (iff p q) (and (imp p q) (imp q p)) := by
    apply ProofTree.leftIff (Γ := ∅) p q isFSet_empty (singleton_sorted ha) hp hq
    have d : AlphaBetaEtaProof {imp p q} {imp p q} := .hypothesis _ hpq
    have e : AlphaBetaEtaProof {imp q p} {imp q p} := .hypothesis _ hqp
    simpa using ProofTree.rightAnd (Γ := {imp p q}) (Ω := {imp q p}) (Δ := ∅) (Ξ := ∅)
      _ _ (singleton_sorted hpq) isFSet_empty (singleton_sorted hqp) isFSet_empty hpq hqp d e
  have backward : Entails (and (imp p q) (imp q p)) (iff p q) := by
    simpa using ProofTree.rightIff (Γ := {and (imp p q) (imp q p)})
      (Ω := {and (imp p q) (imp q p)}) (Δ := ∅) (Ξ := ∅) p q
      (singleton_sorted ha) isFSet_empty (singleton_sorted ha) isFSet_empty hp hq
      (and_left hpq hqp) (and_right hpq hqp)
  exact ContextEq.of_formula (isFormula_iff hp hq) ha ⟨forward⟩ ⟨backward⟩

theorem exists_dual (x : SVar) (hx : x.sort = ind) (hp : isFormula p) :
    ContextEq prop (exists_ x p) (neg (forall_ x (neg p))) := by
  have he := isFormula_exists hx hp
  have hn := isFormula_neg hp
  have ha := isFormula_forall hx hn
  have hna := isFormula_neg ha
  have d := trans hp (isFormula_neg hn) hna (doubleNegIntro hp)
    (neg_mono ha hn (forall_elim x hx hn))
  have forward : Entails (exists_ x p) (neg (forall_ x (neg p))) :=
    .leftExists (Γ := ∅) x p isFSet_empty (singleton_sorted hna) hx hp d
      (by simp [freeVars, HasFree.freeVars, Expr.exists_, Expr.forall_, Expr.neg, Expr.freeVars])
  have introEx : Entails p (exists_ x p) :=
    .rightExists (Δ := ∅) x p (.var x) (singleton_sorted hp) isFSet_empty hx hp
      (by simpa [isTerm, hasSort] using hx)
      (convert hp hp (.refl _) (substOne_self hp x).symm (.hypothesis p hp))
  have backward : Entails (neg (exists_ x p)) (forall_ x (neg p)) :=
    .rightForall (Δ := ∅) x (neg p) (singleton_sorted (isFormula_neg he)) isFSet_empty hx hn
      (neg_mono hp he introEx)
      (by simp [freeVars, HasFree.freeVars, Expr.exists_, Expr.forall_, Expr.neg, Expr.freeVars])
  exact ContextEq.of_formula he hna ⟨forward⟩
    ⟨trans hna (isFormula_neg (isFormula_neg he)) he
      (neg_mono (isFormula_neg he) ha backward) (doubleNegElim he)⟩

end
end Derivation

namespace SimpleExpr

theorem lowerConst_sound (s : LSort) (c : Identifier) :
    ProvableEQ (lowerConst s c) (.const c) := by
  unfold lowerConst
  split
  · exact ProvableEQ.of_toTerm (by simp [toTerm])
  · intro ρ
    simp only [reify_neg, reify_top, reify_const]
    exact ContextEq.of_formula (isFormula_neg rfl) rfl
      ⟨false_of_neg_top⟩ ⟨bot_le (isFormula_neg rfl)⟩
  · exact ProvableEQ.refl _

theorem lowerApp_sound (f : SimpleExpr (s >> t)) (a : SimpleExpr s) :
    ProvableEQ (lowerApp f a) (.app f a) := by
  unfold lowerApp
  split
  · exact ProvableEQ.of_toTerm (by simp [toTerm])
  · exact ProvableEQ.of_toTerm (by simp [toTerm]; rfl)
  · rename_i p q
    intro ρ
    simpa only [reify_neg, reify_conj_pair, reify_app, reify_const] using (or_dual (p.reify_sort ρ) (q.reify_sort ρ)).symm
  · rename_i p q
    intro ρ
    simpa only [reify_neg, reify_conj_pair, reify_app, reify_const] using (imp_dual (p.reify_sort ρ) (q.reify_sort ρ)).symm
  · rename_i p q
    intro ρ
    have hp := p.reify_sort ρ
    have hq := q.reify_sort ρ
    have hs₁ := isFormula_neg (isFormula_and hp (isFormula_neg hq))
    have hs₂ := isFormula_neg (isFormula_and hq (isFormula_neg hp))
    have d := ContextEq.app
      (ContextEq.app_sort (show (Expr.const (SConst.named "and" (prop >> prop >> prop))).hasSort
        (prop >> prop >> prop) from rfl) hs₁)
      (ContextEq.app_sort (show (Expr.const (SConst.named "and" (prop >> prop >> prop))).hasSort
        (prop >> prop >> prop) from rfl) (isFormula_imp hp hq))
      hs₂ (isFormula_imp hq hp)
      (ContextEq.app_right (show (Expr.const (SConst.named "and" (prop >> prop >> prop))).hasSort
        (prop >> prop >> prop) from rfl) hs₁ (isFormula_imp hp hq) (imp_dual hp hq).symm)
      (imp_dual hq hp).symm
    simp only [reify_conj_pair, reify_neg, reify_app, reify_const]
    exact ContextEq.trans (isFormula_and (isFormula_neg (isFormula_and hp (isFormula_neg hq)))
      (isFormula_neg (isFormula_and hq (isFormula_neg hp))))
      (isFormula_and (isFormula_imp hp hq) (isFormula_imp hq hp))
      (isFormula_iff hp hq) d (iff_and hp hq).symm
  · exact ProvableEQ.of_toTerm (by simp [toTerm])
  · exact ProvableEQ.of_toTerm (by simp [toTerm])
  · rename_i p
    intro ρ
    let x := ρ.fresh p.toTerm.freeVars ind
    have hx := ρ.fresh_not_mem p.toTerm.freeVars ind
    have hu := ρ.fresh_not_used p.toTerm.freeVars ind
    have hbody := Lambda.reify_lam_at p.toTerm ρ x hx hu
    have hex : AlphaBetaEta
        ((SimpleExpr.app (t := prop) (.const ⟨"exists", 0⟩) (.lam ind p)).reify ρ)
        (Expr.exists_ x (p.reify (ρ.extend x))) := by
      unfold reify
      rw [toTerm, toTerm, toTerm]
      exact .app (.refl _) (.alpha hbody)
    have hall := (SimpleExpr.neg p).reify_all_at ρ x rfl (by simpa [toTerm, Lambda.Term.freeVars] using hx) hu
    have hdual : AlphaBetaEta ((SimpleExpr.neg (.all (.neg p))).reify ρ)
        (Expr.neg (Expr.forall_ x (Expr.neg (p.reify (ρ.extend x))))) := by
      simpa only [reify_neg] using AlphaBetaEta.app (.refl _) hall
    exact ContextEq.trans (SimpleExpr.reify_sort _ _) (isFormula_neg (isFormula_forall rfl
      (isFormula_neg (p.reify_sort _)))) (SimpleExpr.reify_sort _ _)
      (ContextEq.of_conversion (SimpleExpr.reify_sort _ _) hdual)
      (ContextEq.trans (isFormula_neg (isFormula_forall rfl (isFormula_neg (p.reify_sort _))))
        (isFormula_exists rfl (p.reify_sort _)) (SimpleExpr.reify_sort _ _)
        (exists_dual x rfl (p.reify_sort _)).symm
        (ContextEq.of_conversion (isFormula_exists rfl (p.reify_sort _)) hex.symm))
  · exact ProvableEQ.refl _

/-- Translating a typed expression preserves its meaning in every formula
context, under every assignment of names to ambient indices. -/
theorem ofTerm_sound (e : Lambda.Term s) (ρ : Lambda.Context) :
    ContextEq s ((ofTerm e).reify ρ) (e.reify ρ) := by
  induction e generalizing ρ with
  | bound n =>
      simp only [ofTerm, reify, toTerm]
      exact ContextEq.refl (Lambda.Term.reify_sort _ _)
  | free x =>
      simp only [ofTerm, reify, toTerm]
      exact ContextEq.refl (Lambda.Term.reify_sort _ _)
  | const c =>
      simpa only [ofTerm, reify, toTerm] using lowerConst_sound _ c ρ
  | app f a ihf iha =>
      simp only [ofTerm]
      apply ContextEq.trans (reify_sort _ _) (reify_sort (.app (ofTerm f) (ofTerm a)) _)
        (Lambda.Term.reify_sort _ _) (lowerApp_sound _ _ ρ)
      simpa only [reify_app, Lambda.Term.reify] using
        ContextEq.app (reify_sort _ _) (Lambda.Term.reify_sort f ρ)
          (reify_sort _ _) (Lambda.Term.reify_sort a ρ) (ihf ρ) (iha ρ)
  | lam s b ih =>
      let x := ρ.fresh ((ofTerm b).toTerm.freeVars ∪ b.freeVars) s
      have hx := ρ.fresh_not_mem ((ofTerm b).toTerm.freeVars ∪ b.freeVars) s
      have hu := ρ.fresh_not_used ((ofTerm b).toTerm.freeVars ∪ b.freeVars) s
      have hp : AlphaBetaEta ((ofTerm (.lam s b)).reify ρ)
          (.lam x ((ofTerm b).reify (ρ.extend x))) := by
        simp only [ofTerm, reify, toTerm]
        exact .alpha (Lambda.reify_lam_at (ofTerm b).toTerm ρ x
          (fun h => hx (Finset.mem_union_left _ h)) hu)
      have hq : AlphaBetaEta ((Lambda.Term.lam s b).reify ρ)
          (.lam x (b.reify (ρ.extend x))) :=
        .alpha (Lambda.reify_lam_at b ρ x (fun h => hx (Finset.mem_union_right _ h)) hu)
      have hs := reify_sort (ofTerm (.lam s b)) ρ
      have ht := Lambda.Term.reify_sort (.lam s b) ρ
      have hs' := hp.preserves_sort.symm.trans hs
      have ht' := hq.preserves_sort.symm.trans ht
      exact ContextEq.trans hs hs' ht (ContextEq.of_conversion hs hp)
        (ContextEq.trans hs' ht' ht
          (ContextEq.lam x (reify_sort _ _) (Lambda.Term.reify_sort _ _) (ih (ρ.extend x)))
          (ContextEq.of_conversion ht' hq.symm))

end SimpleExpr
end Lisa.Orthologic
