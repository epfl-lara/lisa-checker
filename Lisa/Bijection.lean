import Lisa.Syntax
import Lisa.Standard
import Lisa.Weakened

open Lisa
open Expr

private theorem isSame_refl {leq : Order} (href : Reflexive leq) (α : Expr) :
    isSame leq α α := by
  exact ⟨href α, href α⟩

private theorem ordContains_refl {leq : Order} (href : Reflexive leq) (α : Expr) (Γ : Finset Expr) :
    ordContains leq α (insert α Γ) := by
  exact ⟨α, by simp, href α⟩

private theorem isFSet_insert {Γ : Finset Expr} {φ : Expr} (hφ : isFormula φ) (hΓ : isFSet Γ) :
    isFSet (insert φ Γ) := by
  intro ψ hψ
  simp only [Finset.mem_insert] at hψ
  rcases hψ with rfl | hψ
  · exact hφ
  · exact hΓ ψ hψ

private theorem isFSet_union {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    isFSet (Γ ∪ Δ) := by
  intro φ hφ
  simp only [Finset.mem_union] at hφ
  rcases hφ with hφ | hφ
  · exact hΓ φ hφ
  · exact hΔ φ hφ

private theorem isFormula_and {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (and α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.and, hα, hβ]

private theorem isFormula_imp {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (imp α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.imp, hα, hβ]

private theorem isFormula_iff {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (iff α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.iff, hα, hβ]

private theorem isFormula_neg {α : Expr} (hα : isFormula α) :
    isFormula (neg α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.neg, hα]

private theorem isFormula_or {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (or α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.or, hα, hβ]

private theorem isFormula_forall {x : SVar} {α : Expr} (hx : x.sort = ind) (hα : isFormula α) :
    isFormula (forall_ x α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.forall_, hx, hα]

private theorem isFormula_eq {s t : Expr} (hs : isTerm s) (ht : isTerm t) :
    isFormula (eq s t) := by
  dsimp [isFormula, hasSort, isTerm] at hs ht ⊢
  simp [Expr.eq, hs, ht]

def fwdEmbed {leq Γ Δ} (href : Reflexive leq) :
    Standard.ProofTree leq Γ Δ ->
    Weakened.ProofTree leq Γ Δ
  | .restate hΓ hΔ hΓ' hΔ' pf hle₁ hle₂ =>
      .restate hΓ hΔ hΓ' hΔ' (fwdEmbed href pf) hle₁ hle₂
  | .weakening hΓ hΔ hΓ' hΔ' pf hle =>
      .weakening hΓ hΔ hΓ' hΔ' (fwdEmbed href pf) hle
  | .hypothesis φ hφ =>
      .hypothesis φ
        (by simp [hφ])
        (by simp [hφ])
        (hφ)
        (ordContains_refl href φ ∅)
        (ordContains_refl href φ ∅)
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      Weakened.ProofTree.cut φ
        hΓ (isFSet_insert hφ hΔ)
        (isFSet_insert hφ hΩ) hΞ
        (isFSet_union hΓ hΩ) (isFSet_union hΔ hΞ)
        hφ
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (Or.inl hχΔ)))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΩ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (Or.inr hχΩ)))
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.leftAnd φ ψ
        (isFSet_insert hφ (isFSet_insert hψ hΓ)) hΔ
        (isFSet_insert (isFormula_and hφ hψ) hΓ) hΔ
        hφ hψ
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχrest
          · rw [hχφ]
            exact Or.inl (isSame_refl href φ)
          · rcases hχrest with hχψ | hχΓ
            · rw [hχψ]
              exact Or.inr (isSame_refl href ψ)
            · exact False.elim (hχnot (by simp [hχΓ])))
        (by
          exact ⟨and φ ψ, by simp, href (and φ ψ)⟩)
  | .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      sorry
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Weakened.ProofTree.leftImp φ ψ
        hΓ (isFSet_insert hφ hΔ)
        (isFSet_insert hψ hΩ) hΞ
        (isFSet_insert (isFormula_imp hφ hψ) (isFSet_union hΓ hΩ)) (isFSet_union hΔ hΞ)
        hφ hψ
        (fwdEmbed href pf₁) (fwdEmbed href pf₂)
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (Or.inl hχΔ)))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχψ | hχΩ
          · rw [hχψ]
            exact isSame_refl href ψ
          · exact False.elim (hχnot (by simp [hχΩ])))
        (by
          exact ⟨imp φ ψ, by simp, href (imp φ ψ)⟩)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.leftIff φ ψ
        (isFSet_insert (isFormula_imp hφ hψ)
          (isFSet_insert (isFormula_imp hψ hφ) hΓ))
        hΔ
        (isFSet_insert (isFormula_iff hφ hψ) hΓ) hΔ
        hφ hψ
        (fwdEmbed href pf)
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχimp | hχrest
          · rw [hχimp]
            exact Or.inl (isSame_refl href (imp φ ψ))
          · rcases hχrest with hχimp | hχΓ
            · rw [hχimp]
              exact Or.inr (isSame_refl href (imp ψ φ))
            · exact False.elim (hχnot (by simp [hχΓ])))
        (by
          exact ⟨iff φ ψ, by simp, href (iff φ ψ)⟩)
  | .leftNot φ hΓ hΔ hφ pf =>
      Weakened.ProofTree.leftNot φ
        hΓ (isFSet_insert hφ hΔ)
        (isFSet_insert (isFormula_neg hφ) hΓ) hΔ
        hφ
        (fwdEmbed href pf)
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot hχΔ))
        (by
          exact ⟨neg φ, by simp, href (neg φ)⟩)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      sorry
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      sorry
  | .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      sorry
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.rightOr φ ψ
        hΓ (isFSet_insert hφ (isFSet_insert hψ hΔ))
        hΓ (isFSet_insert (isFormula_or hφ hψ) hΔ)
        hφ hψ
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχrest
          · rw [hχφ]
            exact Or.inl (isSame_refl href φ)
          · rcases hχrest with hχψ | hχΔ
            · rw [hχψ]
              exact Or.inr (isSame_refl href ψ)
            · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨or φ ψ, by simp, href (or φ ψ)⟩)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.rightImp φ ψ
        (isFSet_insert hφ hΓ) (isFSet_insert hψ hΔ)
        hΓ (isFSet_insert (isFormula_imp hφ hψ) hΔ)
        hφ hψ
        (fwdEmbed href pf)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΓ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot hχΓ))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχψ | hχΔ
          · rw [hχψ]
            exact isSame_refl href ψ
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨imp φ ψ, by simp, href (imp φ ψ)⟩)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Weakened.ProofTree.rightIff φ ψ
        hΓ (isFSet_insert (isFormula_imp hφ hψ) hΔ)
        hΩ (isFSet_insert (isFormula_imp hψ hφ) hΞ)
        (isFSet_union hΓ hΩ) (isFSet_insert (isFormula_iff hφ hψ) (isFSet_union hΔ hΞ))
        hφ hψ
        (fwdEmbed href pf₁) (fwdEmbed href pf₂)
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχimp | hχΔ
          · rw [hχimp]
            exact isSame_refl href (imp φ ψ)
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχimp | hχΞ
          · rw [hχimp]
            exact isSame_refl href (imp ψ φ)
          · exact False.elim (hχnot (by simp [hχΞ])))
        (by
          exact ⟨iff φ ψ, by simp, href (iff φ ψ)⟩)
  | .rightNot φ hΓ hΔ hφ pf =>
      Weakened.ProofTree.rightNot φ
        (isFSet_insert hφ hΓ) hΔ
        hΓ (isFSet_insert (isFormula_neg hφ) hΔ)
        hφ
        (fwdEmbed href pf)
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΓ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot hχΓ))
        (by
          exact ⟨neg φ, by simp, href (neg φ)⟩)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      Weakened.ProofTree.rightForall x φ
        hΓ (isFSet_insert hφ hΔ)
        hΓ (isFSet_insert (isFormula_forall hx hφ) hΔ)
        hx hφ
        (fwdEmbed href pf)
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨forall_ x φ, by simp, href (forall_ x φ)⟩)
        (by
          have hsets : insert (forall_ x φ) Γ ∪ Δ = Γ ∪ insert (forall_ x φ) Δ := by
            ext χ
            simp [or_assoc, or_comm]
          simpa [hsets] using hfree)
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      sorry
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      sorry
  | .leftRefl t hΓ hΔ ht pf =>
      Weakened.ProofTree.leftRefl t
        (isFSet_insert (isFormula_eq ht ht) hΓ) hΔ
        hΓ hΔ
        ht
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχeq | hχΓ
          · rw [hχeq]
            exact isSame_refl href (eq t t)
          · exact False.elim (hχnot hχΓ))
  | .rightRefl t ht =>
      Weakened.ProofTree.rightRefl t
        (show isFSet (∅ : Finset Expr) from by
          intro φ hφ
          simp at hφ)
        (isFSet_insert (isFormula_eq ht ht) (show isFSet (∅ : Finset Expr) from by
          intro φ hφ
          simp at hφ))
        ht
        (ordContains_refl href (eq t t) ∅)
  | .leftSubstEq x s t φ hΓ hΔ hx hs ht hφ pf =>
      .leftSubstEq x s t φ hΓ hΔ hx hs ht hφ (fwdEmbed href pf)
  | .rightSubstEq x s t φ hΓ hΔ hx hs ht hφ pf =>
      .rightSubstEq x s t φ hΓ hΔ hx hs ht hφ (fwdEmbed href pf)
  | .instSchema σ hΓ hΔ hσ pf =>
      .instSchema σ hΓ hΔ hσ (fwdEmbed href pf)

def bwdEmbed  {leq Γ Δ} (href : Reflexive leq) :
    Weakened.ProofTree leq Γ Δ ->
    Standard.ProofTree leq Γ Δ
  | .restate hΓ hΔ hΓ' hΔ' pf hle₁ hle₂ =>
      Standard.ProofTree.restate hΓ hΔ hΓ' hΔ' (bwdEmbed href pf) hle₁ hle₂
  | .weakening hΓ hΔ hΓ' hΔ' pf hle =>
      Standard.ProofTree.weakening hΓ hΔ hΓ' hΔ' (bwdEmbed href pf) hle
  | .hypothesis α hΩ₁ hΩ₂ hα hleft hright =>
      sorry
  | .cut α hΓ₁ hΓ₂ hΔ₁ hΔ₂ hΩ₁ hΩ₂ hα hsub₁ hsub₂ hrem₁ hrem₂ =>
      sorry
  | .leftAnd α β hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      sorry
  | .leftOr hne hsorted hprems hpreserved hadd =>
      sorry
  | .leftImp α β hΓ₁ hΓ₂ hΔ₁ hΔ₂ hΩ₁ hΩ₂ hα hβ pf₁ pf₂ hsub₁ hsub₂ hrem₁ hrem₂ hadd =>
      sorry
  | .leftIff α β hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα hβ pf hsub hrem hadd =>
      sorry
  | .leftNot α hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα pf hsub hrem hadd =>
      sorry
  | .leftForall x α t hΓ₁ hΓ₂ hΩ₁ hΩ₂ hx hα ht pf hsub hrem hadd =>
      sorry
  | .leftExists x α hΓ₁ hΓ₂ hΩ₁ hΩ₂ hx hα pf hsub hrem hadd hfree =>
      sorry
  | .rightAnd hne hsorted hprems hpreserved hadd =>
      sorry
  | .rightOr α β hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      sorry
  | .rightImp α β hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα hβ pf hrem₁ hrem₂ hadd =>
      sorry
  | .rightIff α β hΓ₁ hΓ₂ hΔ₁ hΔ₂ hΩ₁ hΩ₂ hα hβ pf₁ pf₂ hsub₁ hsub₂ hrem₁ hrem₂ hadd =>
      sorry
  | .rightNot α hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα pf hsub hrem hadd =>
      sorry
  | .rightForall x α hΓ₁ hΓ₂ hΩ₁ hΩ₂ hx hα pf hsub hrem hadd hfree =>
      sorry
  | .rightExists x α t hΓ₁ hΓ₂ hΩ₁ hΩ₂ hx hα ht pf hsub hrem hadd =>
      sorry
  | .rightEpsilon x α t hΓ₁ hΓ₂ hΩ₁ hΩ₂ hx hα ht pf hsub hrem hadd =>
      sorry
  | .leftRefl t hΓ₁ hΓ₂ hΩ₁ hΩ₂ ht hsub hrem =>
      sorry
  | .rightRefl t hΩ₁ hΩ₂ ht hadd =>
      sorry
  | .leftSubstEq x s t φ hΓ hΔ hx hs ht hφ pf =>
      Standard.ProofTree.leftSubstEq x s t φ hΓ hΔ hx hs ht hφ (bwdEmbed href pf)
  | .rightSubstEq x s t φ hΓ hΔ hx hs ht hφ pf =>
      Standard.ProofTree.rightSubstEq x s t φ hΓ hΔ hx hs ht hφ (bwdEmbed href pf)
  | .instSchema σ hΓ hΔ hσ pf =>
      Standard.ProofTree.instSchema σ hΓ hΔ hσ (bwdEmbed href pf)

theorem standard_eq_weakened (leq : Order) (Γ Δ : Finset Expr) (href : Reflexive leq) :
    Nonempty (Standard.ProofTree leq Γ Δ) ↔
    Nonempty (Weakened.ProofTree leq Γ Δ) := by
  constructor <;> intro ⟨pf⟩
  · exact ⟨fwdEmbed href pf⟩
  · exact ⟨bwdEmbed href pf⟩
