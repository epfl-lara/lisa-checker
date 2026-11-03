import Lisa.LambdaFol.WithoutInstantiation
import Lisa.LambdaFol.ToPureFol.FormulaClasses
/-! Assemble and project the conjunction in a simultaneous replacement premise. -/
noncomputable section
namespace Lisa.LambdaFol.WithoutInstantiation
open Expr

theorem andFold_sorted (es : List Expr) (p : Expr) (hp : isFormula p)
    (hs : ∀ e ∈ es, isFormula e) : isFormula (es.foldl Expr.and p) := by
  induction es generalizing p with
  | nil => exact hp
  | cons e es ih =>
      exact ih (and p e) (isFormula_and hp (hs e (by simp))) (fun q hq => hs q (by simp [hq]))

theorem conjunction_sorted (es : List Expr) (hs : ∀ e ∈ es, isFormula e) :
    isFormula (foldFormulas Expr.and top es) := by
  cases es with
  | nil => rfl
  | cons p ps => exact andFold_sorted ps p (hs p (by simp)) (fun q hq => hs q (by simp [hq]))

namespace ProofTree
variable {Γ Δ : Finset Formula}

def consequence {p q : Formula} (d : ProofTree Γ (insert p Δ))
    (h : ProofTree {p} {q}) : ProofTree Γ (insert q Δ) := by
  have c := ProofTree.cut (Γ₁ := ∅) (Δ₁ := {q}) p d (by simpa using h)
  simpa [Finset.union_comm] using c

def andLeft (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
    ProofTree {ofExpr (and p q) (isFormula_and hp hq)} {ofExpr p hp} :=
  .leftAnd (Γ := ∅) p q hp hq (.weakening (.hypothesis (ofExpr p hp)) (by simp) (by simp))

def andRight (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
    ProofTree {ofExpr (and p q) (isFormula_and hp hq)} {ofExpr q hq} :=
  .leftAnd (Γ := ∅) p q hp hq (.weakening (.hypothesis (ofExpr q hq)) (by simp) (by simp))

def andFold_project (es : List Expr) (p : Expr) (hp : isFormula p)
    (hs : ∀ e ∈ es, isFormula e) (q : Expr) (hq : isFormula q) (hm : q = p ∨ q ∈ es) :
    ProofTree {ofExpr (es.foldl Expr.and p) (andFold_sorted es p hp hs)} {ofExpr q hq} := by
  -- Start from the selected hypothesis, then combine assumptions with leftAnd.
  have collect (es : List Expr) (p : Expr) (hp : isFormula p)
      (hs : ∀ e ∈ es, isFormula e)
      (d : ProofTree (insert (ofExpr p hp)
        (formulaSet es.toFinset (fun e he => hs e (by simpa using he)))) {ofExpr q hq}) :
      ProofTree {ofExpr (es.foldl Expr.and p) (andFold_sorted es p hp hs)} {ofExpr q hq} := by
    induction es generalizing p with
    | nil => simpa using d
    | cons e es ih =>
        exact ih (and p e) (isFormula_and hp (hs e (by simp)))
          (fun r hr => hs r (by simp [hr]))
          (.leftAnd p e hp (hs e (by simp)) (by simpa using d))
  apply collect es p hp hs
  apply ProofTree.weakening (.hypothesis (ofExpr q hq)) _ (Finset.Subset.refl _)
  apply Finset.singleton_subset_iff.mpr
  rcases hm with rfl | hm
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((mem_formulaSet _ _).mpr ⟨q, by simpa using hm, rfl⟩)

def conjunction_project (es : List Expr) (hs : ∀ e ∈ es, isFormula e)
    (q : Expr) (hq : q ∈ es) :
    ProofTree {ofExpr (foldFormulas Expr.and top es) (conjunction_sorted es hs)}
      {ofExpr q (hs q hq)} := by
  cases es with
  | nil => simp at hq
  | cons p ps =>
      exact andFold_project ps p (hs p (by simp)) (fun q hq => hs q (by simp [hq]))
        q (hs q hq) (by simpa using hq)

def andFold_intro (es : List Expr) (p : Expr) (hp : isFormula p)
    (hs : ∀ e ∈ es, isFormula e) (d : ProofTree Γ (insert (ofExpr p hp) Δ))
    (ds : ∀ e (he : e ∈ es), ProofTree Γ (insert (ofExpr e (hs e he)) Δ)) :
    ProofTree Γ (insert (ofExpr (es.foldl Expr.and p) (andFold_sorted es p hp hs)) Δ) := by
  induction es generalizing p with
  | nil => exact d
  | cons e es ih =>
      have he := hs e (by simp)
      apply ih (and p e) (isFormula_and hp he) (fun q hq => hs q (by simp [hq]))
      · simpa using ProofTree.rightAnd p e hp he d (ds e (by simp))
      · intro q hq; exact ds q (by simp [hq])

def conjunction_intro (es : List Expr) (hs : ∀ e ∈ es, isFormula e)
    (ds : ∀ e (he : e ∈ es), ProofTree Γ (insert (ofExpr e (hs e he)) Δ)) :
    ProofTree Γ (insert (ofExpr (foldFormulas Expr.and top es) (conjunction_sorted es hs)) Δ) := by
  cases es with
  | nil => exact .weakening .rightTrue (by simp) (by simp [foldFormulas])
  | cons p ps =>
      exact andFold_intro ps p (hs p (by simp)) (fun q hq => hs q (by simp [hq]))
        (ds p (by simp)) (fun q hq => ds q (by simp [hq]))

end ProofTree
end Lisa.LambdaFol.WithoutInstantiation
