import Lisa.SCLambdaToPure.EmbeddingRules

/-! Rule-by-rule interpretation of pure first-order proofs in system A. -/

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder

noncomputable def context (η : Nat → Identifier) (Γ : Pure.Context Readback.language) : A.Context :=
  Γ.image (ofFormula η)

@[simp] theorem context_empty : context η ∅ = ∅ := Finset.image_empty _
@[simp] theorem context_insert (p : Pure.Formula Readback.language) (Γ : Pure.Context Readback.language) :
    context η (insert p Γ) = insert (ofFormula η p) (context η Γ) := Finset.image_insert _ _ _
@[simp] theorem context_union (Γ Δ : Pure.Context Readback.language) :
    context η (Γ ∪ Δ) = context η Γ ∪ context η Δ := Finset.image_union _ _

noncomputable def toAWithAxioms (η : Nat → Identifier) (hη : Function.Injective η)
    {U : Readback.language.Theory} {T : A.Theory}
    (axioms : ∀ p ∈ U, A.ProofTree T ∅ {ofFormula η (Pure.ofSentence p)})
    {Γ Δ : Pure.Context Readback.language} (d : Pure.ProofTree U Γ Δ) :
    A.ProofTree T (context η Γ) (context η Δ) := by
  induction d with
  | hypothesis p => simpa [context] using A.ProofTree.hypothesis (T := T) (ofFormula η p)
  | theoryAxiom h => simpa [context] using axioms _ h
  | weakening _ hΓ hΔ ih =>
      exact .weakening ih (Finset.image_subset_image hΓ) (Finset.image_subset_image hΔ)
  | cut p _ _ ih₁ ih₂ =>
      simpa using A.ProofTree.cut (ofFormula η p) (by simpa using ih₁) (by simpa using ih₂)
  | leftFalse => simpa [context] using (A.ProofTree.leftFalse (T := T))
  | rightTrue => simpa [context] using (rightTop (T := T) (η := η))
  | leftAnd p q _ ih => simpa using leftAnd p q (by simpa using ih)
  | rightAnd p q _ _ ih₁ ih₂ => simpa using rightAnd p q (by simpa using ih₁) (by simpa using ih₂)
  | leftOr p q _ _ ih₁ ih₂ => simpa using leftOr p q (by simpa using ih₁) (by simpa using ih₂)
  | rightOr p q _ ih => simpa using rightOr p q (by simpa using ih)
  | leftImp p q _ _ ih₁ ih₂ => simpa using leftImp p q (by simpa using ih₁) (by simpa using ih₂)
  | rightImp p q _ ih => simpa using rightImp p q (by simpa using ih)
  | leftNot p _ ih => simpa using leftNot p (by simpa using ih)
  | rightNot p _ ih => simpa using rightNot p (by simpa using ih)
  | leftForall x p t _ ih => simpa using leftAll hη x p t (by simpa using ih)
  | rightForall x p _ hΓ hΔ ih =>
      simpa using rightAll hη x p (by simpa using ih) (fresh η hη x _ hΓ) (fresh η hη x _ hΔ)
  | leftExists x p _ hΓ hΔ ih =>
      simpa using leftExists hη x p (by simpa using ih) (fresh η hη x _ hΓ) (fresh η hη x _ hΔ)
  | rightExists x p t _ ih => simpa using rightExists hη x p t (by simpa using ih)
  | refl t =>
      simpa [context, ofFormula_equal] using A.ProofTree.refl (T := T) (namedTerm η t) (namedTerm_sort η t)
  | leftSubst x p t u _ _ ih₁ ih₂ =>
      simpa [ofFormula_subst η hη, ofFormula_equal] using
        A.ProofTree.leftSubst ⟨η x, ind⟩ (namedFormula η p) (namedTerm η t) (namedTerm η u)
          rfl (namedFormula_sort η p) (namedTerm_sort η t) (namedTerm_sort η u)
          (by simpa [ofFormula_subst η hη] using ih₁) (by simpa [ofFormula_equal] using ih₂)
  | rightSubst x p t u _ _ ih₁ ih₂ =>
      simpa [ofFormula_subst η hη, ofFormula_equal] using
        A.ProofTree.rightSubst ⟨η x, ind⟩ (namedFormula η p) (namedTerm η t) (namedTerm η u)
          rfl (namedFormula_sort η p) (namedTerm_sort η t) (namedTerm_sort η u)
          (by simpa [ofFormula_subst η hη] using ih₁) (by simpa [ofFormula_equal] using ih₂)

noncomputable def toA (η : Nat → Identifier) (hη : Function.Injective η)
    {Γ Δ : Pure.Context Readback.language} (d : Pure.ProofTree ∅ Γ Δ) :
    A.ProofTree ∅ (context η Γ) (context η Δ) :=
  toAWithAxioms η hη (fun _ h => False.elim h) d

end Lisa.SCLambdaToPure.Embedding
