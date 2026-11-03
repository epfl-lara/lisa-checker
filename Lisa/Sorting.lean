import Lisa.Syntax

/-! Sorting lemmas shared by proof translations and sequent encoding. -/
namespace Lisa
open Expr

theorem isFSet_insert {Γ : Finset Expr} {φ : Expr} (hφ : isFormula φ) (hΓ : isFSet
    Γ) :
    isFSet (insert φ Γ) := by
  simpa only [isFSet, Finset.forall_mem_insert] using And.intro hφ hΓ

theorem isFSet_empty :
    isFSet (∅ : Finset Expr) := by simp [isFSet]

theorem isFSet_union {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    isFSet (Γ ∪ Δ) := by
  simpa only [isFSet, Finset.forall_mem_union] using And.intro hΓ hΔ

theorem isFormula_and {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (and α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.and, hα, hβ]

theorem isFormula_imp {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (imp α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.imp, hα, hβ]

theorem isFormula_iff {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (iff α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.iff, hα, hβ]

theorem isFormula_neg {α : Expr} (hα : isFormula α) :
    isFormula (neg α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.neg, hα]

theorem isFormula_or {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (or α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.or, hα, hβ]

theorem isFormula_forall {x : SVar} {α : Expr} (hx : x.sort = ind) (hα : isFormula
    α) :
    isFormula (forall_ x α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.forall_, hx, hα]

theorem isFormula_exists {x : SVar} {α : Expr} (hx : x.sort = ind) (hα : isFormula
    α) :
    isFormula (exists_ x α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.exists_, hx, hα]

theorem isTerm_epsilon {x : SVar} {α : Expr} (hx : x.sort = ind) (hα : isFormula α)
    :
    isTerm (epsilon_ (.lam x α)) := by
  dsimp [isTerm, hasSort, isFormula] at hα ⊢
  simp [Expr.epsilon_, hx, hα]

theorem isFormula_substOne {x : SVar} {t α : Expr}
    (hx : x.sort = ind) (ht : isTerm t) (hα : isFormula α) :
    isFormula (substOne x t α) := by
  unfold Expr.substOne Expr.subst
  apply Subst.subst_preserves_hasSort
  · apply Subst.wellSorted_insert
    · simp
    · rwa [hx]
  · exact hα

theorem isFormula_eq {s t : Expr} (hs : isTerm s) (ht : isTerm t) :
    isFormula (eq s t) := by
  dsimp [isFormula, hasSort, isTerm] at hs ht ⊢
  simp [Expr.eq, hs, ht]

end Lisa
