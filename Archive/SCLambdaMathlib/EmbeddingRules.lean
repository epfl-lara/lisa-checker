import Lisa.SCLambdaToPure.EmbeddingSupport

/-! Mathlib encodes its derived connectives using implication and falsity.
These admissible rules construct A proofs of those encodings. -/

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder

variable {η : Nat → Identifier} {T : A.Theory} {Γ Δ Γ' Δ' : A.Context}

def rightImp (p q : Pure.Formula Readback.language)
    (d : A.ProofTree T (insert (ofFormula η p) Γ) (insert (ofFormula η q) Δ)) :
    A.ProofTree T Γ (insert (ofFormula η (p.imp q)) Δ) := by
  rw [ofFormula_imp]
  exact .rightImp _ _ (namedFormula_sort η p) (namedFormula_sort η q) d

def leftImp (p q : Pure.Formula Readback.language)
    (d : A.ProofTree T Γ (insert (ofFormula η p) Δ))
    (e : A.ProofTree T (insert (ofFormula η q) Γ') Δ') :
    A.ProofTree T (insert (ofFormula η (p.imp q)) (Γ ∪ Γ')) (Δ ∪ Δ') := by
  rw [ofFormula_imp]
  exact .leftImp _ _ (namedFormula_sort η p) (namedFormula_sort η q) d e

noncomputable def rightNot (p : Pure.Formula Readback.language)
    (d : A.ProofTree T (insert (ofFormula η p) Γ) Δ) :
    A.ProofTree T Γ (insert (ofFormula η p.not) Δ) :=
  rightImp p ⊥ (.weakening d (by simp) (by simp))

noncomputable def leftNot (p : Pure.Formula Readback.language)
    (d : A.ProofTree T Γ (insert (ofFormula η p) Δ)) :
    A.ProofTree T (insert (ofFormula η p.not) Γ) Δ := by
  simpa using leftImp p ⊥ d
    (show A.ProofTree T (insert (ofFormula η ⊥) ∅) ∅ from by simpa using A.ProofTree.leftFalse)

noncomputable def rightTop : A.ProofTree T ∅ {ofFormula η ⊤} := by
  simpa using rightImp (η := η) (Γ := ∅) (Δ := ∅) ⊥ ⊥
    (by simpa using A.ProofTree.hypothesis (T := T) (ofFormula η ⊥))

noncomputable def leftAnd (p q : Pure.Formula Readback.language)
    (d : A.ProofTree T (insert (ofFormula η p) (insert (ofFormula η q) Γ)) Δ) :
    A.ProofTree T (insert (ofFormula η (p ⊓ q)) Γ) Δ := by
  apply leftNot
  apply rightImp p q.not
  apply rightNot q
  simpa [Finset.insert_comm] using d

noncomputable def rightAnd (p q : Pure.Formula Readback.language)
    (d : A.ProofTree T Γ (insert (ofFormula η p) Δ))
    (e : A.ProofTree T Γ' (insert (ofFormula η q) Δ')) :
    A.ProofTree T (Γ ∪ Γ') (insert (ofFormula η (p ⊓ q)) (Δ ∪ Δ')) := by
  apply rightNot
  simpa using leftImp p q.not d (leftNot q e)

noncomputable def leftOr (p q : Pure.Formula Readback.language)
    (d : A.ProofTree T (insert (ofFormula η p) Γ) Δ)
    (e : A.ProofTree T (insert (ofFormula η q) Γ') Δ') :
    A.ProofTree T (insert (ofFormula η (p ⊔ q)) (Γ ∪ Γ')) (Δ ∪ Δ') :=
  leftImp p.not q (rightNot p d) e

noncomputable def rightOr (p q : Pure.Formula Readback.language)
    (d : A.ProofTree T Γ (insert (ofFormula η p) (insert (ofFormula η q) Δ))) :
    A.ProofTree T Γ (insert (ofFormula η (p ⊔ q)) Δ) :=
  rightImp p.not q (leftNot p d)

def leftAll (hη : Function.Injective η) (x : Nat) (p : Pure.Formula Readback.language)
    (t : Pure.Term Readback.language)
    (d : A.ProofTree T (insert (ofFormula η (Pure.substOne x t p)) Γ) Δ) :
    A.ProofTree T (insert (ofFormula η (Pure.forall_ x p)) Γ) Δ := by
  rw [ofFormula_all η hη]
  rw [ofFormula_subst η hη] at d
  exact .leftForall ⟨η x, ind⟩ (namedFormula η p) (namedTerm η t) rfl
    (namedFormula_sort η p) (namedTerm_sort η t) d

def rightAll (hη : Function.Injective η) (x : Nat) (p : Pure.Formula Readback.language)
    (d : A.ProofTree T Γ (insert (ofFormula η p) Δ))
    (hΓ : A.Fresh ⟨η x, ind⟩ Γ) (hΔ : A.Fresh ⟨η x, ind⟩ Δ) :
    A.ProofTree T Γ (insert (ofFormula η (Pure.forall_ x p)) Δ) := by
  rw [ofFormula_all η hη]
  exact .rightForall ⟨η x, ind⟩ (namedFormula η p) rfl (namedFormula_sort η p) d hΓ hΔ

private theorem subst_not (x : Nat) (t : Pure.Term Readback.language) (p : Pure.Formula Readback.language) :
    Pure.substOne x t p.not = (Pure.substOne x t p).not := rfl

private theorem exists_encoding (x : Nat) (p : Pure.Formula Readback.language) :
    Pure.exists_ x p = (Pure.forall_ x p.not).not := by
  simp [Pure.exists_, Pure.forall_, Pure.bind, Language.BoundedFormula.ex]

noncomputable def rightExists (hη : Function.Injective η) (x : Nat)
    (p : Pure.Formula Readback.language) (t : Pure.Term Readback.language)
    (d : A.ProofTree T Γ (insert (ofFormula η (Pure.substOne x t p)) Δ)) :
    A.ProofTree T Γ (insert (ofFormula η (Pure.exists_ x p)) Δ) := by
  rw [exists_encoding]
  apply rightNot
  apply leftAll hη x p.not t
  simpa only [subst_not] using leftNot (Pure.substOne x t p) d

noncomputable def leftExists (hη : Function.Injective η) (x : Nat)
    (p : Pure.Formula Readback.language)
    (d : A.ProofTree T (insert (ofFormula η p) Γ) Δ)
    (hΓ : A.Fresh ⟨η x, ind⟩ Γ) (hΔ : A.Fresh ⟨η x, ind⟩ Δ) :
    A.ProofTree T (insert (ofFormula η (Pure.exists_ x p)) Γ) Δ := by
  rw [exists_encoding]
  exact leftNot _ (rightAll hη x p.not (rightNot p d) hΓ hΔ)

end Lisa.SCLambdaToPure.Embedding
