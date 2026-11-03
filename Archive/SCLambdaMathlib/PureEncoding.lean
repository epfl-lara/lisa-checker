import Lisa.SCLambdaToPure.PureCongruence

/-! Compressing a finite sequent into one implication and expanding it again.
All steps are derivations in the first-order calculus. -/
namespace Lisa.SCLambdaToPure.PureSyntax
open FirstOrder
variable {L : Language.{0, 0}} {mode : Mode} [DecidableEq (Formula L mode)]
variable {T : Theory L mode} {Γ Δ : Context L mode}

def conjoin : List (Formula L mode) → Formula L mode
  | [] => .top
  | a :: as => as.foldl BFormula.and a

def disjoin : List (Formula L mode) → Formula L mode
  | [] => .bot
  | a :: as => as.foldl BFormula.or a

namespace ProofTree

def conjoin_left (es : List (Formula L mode))
    (d : ProofTree T (es.toFinset ∪ Γ) Δ) : ProofTree T (insert (conjoin es) Γ) Δ := by
  have go (xs : List (Formula L mode)) : ∀ a,
      ProofTree T (insert a (xs.toFinset ∪ Γ)) Δ →
      ProofTree T (insert (xs.foldl BFormula.and a) Γ) Δ := by
    induction xs with
    | nil => intro a d; simpa using d
    | cons b bs ih =>
        intro a d
        exact ih (.and a b) (.leftAnd a b (by simpa using d))
  cases es with
  | nil => exact d.weakening (by simp) (Finset.Subset.refl _)
  | cons a es => exact go es a (by simpa using d)

def disjoin_right (es : List (Formula L mode))
    (d : ProofTree T Γ (es.toFinset ∪ Δ)) : ProofTree T Γ (insert (disjoin es) Δ) := by
  have go (xs : List (Formula L mode)) : ∀ a,
      ProofTree T Γ (insert a (xs.toFinset ∪ Δ)) →
      ProofTree T Γ (insert (xs.foldl BFormula.or a) Δ) := by
    induction xs with
    | nil => intro a d; simpa using d
    | cons b bs ih =>
        intro a d
        exact ih (.or a b) (.rightOr a b (by simpa using d))
  cases es with
  | nil => exact d.weakening (Finset.Subset.refl _) (by simp)
  | cons a es => exact go es a (by simpa using d)

def conjoin_right (es : List (Formula L mode)) : ProofTree T es.toFinset {conjoin es} := by
  have go (Γ : Context L mode) (xs : List (Formula L mode)) : ∀ a,
      ProofTree T Γ {a} → (∀ b ∈ xs, b ∈ Γ) → ProofTree T Γ {xs.foldl BFormula.and a} := by
    induction xs with
    | nil => intro a d _; exact d
    | cons b bs ih =>
        intro a d h
        have hb : ProofTree T Γ {b} := hypothesisIn b (h b (by simp)) (by simp)
        apply ih (.and a b) (by simpa using ProofTree.rightAnd (Δ := ∅) (Ξ := ∅) a b d hb)
        intro c hc; exact h c (by simp [hc])
  cases es with
  | nil => exact .rightTrue
  | cons a es =>
      exact go (a :: es).toFinset es a (hypothesisIn a (by simp) (by simp)) (by intro b hb; simp [hb])

def disjoin_left (es : List (Formula L mode)) : ProofTree T {disjoin es} es.toFinset := by
  have go (Δ : Context L mode) (xs : List (Formula L mode)) : ∀ a,
      ProofTree T {a} Δ → (∀ b ∈ xs, b ∈ Δ) → ProofTree T {xs.foldl BFormula.or a} Δ := by
    induction xs with
    | nil => intro a d _; exact d
    | cons b bs ih =>
        intro a d h
        have hb : ProofTree T {b} Δ := hypothesisIn b (by simp) (h b (by simp))
        apply ih (.or a b) (by simpa using ProofTree.leftOr (Γ := ∅) (Θ := ∅) a b d hb)
        intro c hc; exact h c (by simp [hc])
  cases es with
  | nil => exact .leftFalse
  | cons a es =>
      exact go (a :: es).toFinset es a (hypothesisIn a (by simp) (by simp)) (by intro b hb; simp [hb])

def encode (as bs : List (Formula L mode)) (d : ProofTree T as.toFinset bs.toFinset) :
    ProofTree T ∅ {.imp (conjoin as) (disjoin bs)} := by
  have right := disjoin_right (Γ := as.toFinset) (Δ := ∅) bs (by simpa using d)
  have both := conjoin_left (Γ := ∅) (Δ := {disjoin bs}) as (by simpa using right)
  simpa using ProofTree.rightImp (Γ := ∅) (Δ := ∅) (conjoin as) (disjoin bs) both

def decode (as bs : List (Formula L mode))
    (d : ProofTree T ∅ {.imp (conjoin as) (disjoin bs)}) :
    ProofTree T as.toFinset bs.toFinset := by
  have h := ProofTree.leftImp (T := T) (Δ := ∅) (Θ := ∅) (conjoin as) (disjoin bs)
    (conjoin_right as) (disjoin_left bs)
  simpa using ProofTree.cut (Γ := ∅) (Δ := ∅) (.imp (conjoin as) (disjoin bs)) d h

end ProofTree
end Lisa.SCLambdaToPure.PureSyntax
