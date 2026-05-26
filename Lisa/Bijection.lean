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
      .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (fwdEmbed href pf₁) (fwdEmbed href pf₂)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      .rightOr φ ψ hΓ hΔ hφ hψ (fwdEmbed href pf)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      .rightImp φ ψ hΓ hΔ hφ hψ (fwdEmbed href pf)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (fwdEmbed href pf₁) (fwdEmbed href pf₂)
  | .rightNot φ hΓ hΔ hφ pf =>
      .rightNot φ hΓ hΔ hφ (fwdEmbed href pf)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      .rightForall x φ hΓ hΔ hx hφ (fwdEmbed href pf) hfree
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      .rightExists x φ t hΓ hΔ hx hφ ht (fwdEmbed href pf)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      .rightEpsilon x φ t hΓ hΔ hx hφ ht (fwdEmbed href pf)
  | .leftRefl t hΓ hΔ ht pf =>
      .leftRefl t hΓ hΔ ht (fwdEmbed href pf)
  | .rightRefl t ht =>
      .rightRefl t ht
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
  | .leftOr α β hne hsorted hα hβ hprems hpreserved hadd =>
      sorry
  | .leftImp α β hΓ₁ hΓ₂ hΔ₁ hΔ₂ hΩ₁ hΩ₂ hα hβ pf₁ pf₂ hsub₁ hsub₂ hrem₁ hrem₂ hadd =>
      sorry
  | .leftIff α β hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα hβ pf hsub hrem hadd =>
      sorry
  | .leftNot α hΓ₁ hΓ₂ hΩ₁ hΩ₂ hα pf hsub hrem hadd =>
      sorry
  | .leftForall x α t hΓ₁ hΓ₂ hΩ₁ hΩ₂ hx hα ht pf hsub γ hmem hsame hadd =>
      sorry
  | .leftExists x α hΓ₁ hΓ₂ hΩ₁ hΩ₂ hx hα pf hsub γ hmem hsame hadd hfree =>
      sorry
  | .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Standard.ProofTree.rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (bwdEmbed href pf₁) (bwdEmbed href pf₂)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      Standard.ProofTree.rightOr φ ψ hΓ hΔ hφ hψ (bwdEmbed href pf)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      Standard.ProofTree.rightImp φ ψ hΓ hΔ hφ hψ (bwdEmbed href pf)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Standard.ProofTree.rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (bwdEmbed href pf₁) (bwdEmbed href pf₂)
  | .rightNot φ hΓ hΔ hφ pf =>
      Standard.ProofTree.rightNot φ hΓ hΔ hφ (bwdEmbed href pf)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      Standard.ProofTree.rightForall x φ hΓ hΔ hx hφ (bwdEmbed href pf) hfree
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      Standard.ProofTree.rightExists x φ t hΓ hΔ hx hφ ht (bwdEmbed href pf)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      Standard.ProofTree.rightEpsilon x φ t hΓ hΔ hx hφ ht (bwdEmbed href pf)
  | .leftRefl t hΓ hΔ ht pf =>
      Standard.ProofTree.leftRefl t hΓ hΔ ht (bwdEmbed href pf)
  | .rightRefl t ht =>
      Standard.ProofTree.rightRefl t ht
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
