import Lisa.SCLambdaToPure.AToPure.FormulaClasses
/-! Assemble and project the conjunction in a simultaneous replacement premise. -/
noncomputable section
namespace Lisa.SCLambdaToPure.A
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
variable {Γ Δ : Context}

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
  induction es generalizing p q with
  | nil =>
      have he : q = p := by simpa using hm
      subst q; exact .hypothesis _
  | cons e es ih =>
      have he := hs e (by simp)
      have ht : ∀ q ∈ es, isFormula q := fun q hq => hs q (by simp [hq])
      by_cases hqp : q = p
      · subst q
        exact consequence (Δ := ∅) (ih (and p e) (isFormula_and hp he) ht _ (isFormula_and hp he) (Or.inl rfl))
          (andLeft p e hp he)
      · have hmem : q ∈ e :: es := hm.resolve_left hqp
        by_cases hqe : q = e
        · subst e
          exact consequence (Δ := ∅) (ih (and p q) (isFormula_and hp hq) ht _ (isFormula_and hp hq) (Or.inl rfl))
            (andRight p q hp hq)
        · exact ih (and p e) (isFormula_and hp he) ht q hq (Or.inr ((List.mem_cons.mp hmem).resolve_left hqe))

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
end Lisa.SCLambdaToPure.A
