import Lisa.SCLambdaToPure.OrderedToA.B
import Lisa.OrderedEncoding

/-! Packing a sequent into its formula is a derivation, not an additional rule.
This accounts for Ordered's whole-sequent restatement when passing to B. -/
noncomputable section
namespace Lisa.SCLambdaToPure.B
open Expr A

private def packAnd (es : List Expr) (a : Expr) (ha : isFormula a)
    (hs : isFSet es.toFinset) {Δ : A.Context}
    (d : ProofTree (insert (ofExpr a ha) (A.context es.toFinset hs)) Δ) :
    ProofTree {ofExpr (es.foldl Expr.and a)
      (A.andFold_sorted es a ha (fun e he => hs e (by simpa using he)))} Δ := by
  induction es generalizing a with
  | nil => simpa using d
  | cons e es ih =>
      have he := hs e (by simp)
      have ht : isFSet es.toFinset := fun q hq => hs q (by simp [hq])
      exact ih (and a e) (isFormula_and ha he) ht
        (.leftAnd a e ha he (by simpa using d))

private theorem orFold_sorted (es : List Expr) (a : Expr) (ha : isFormula a)
    (hs : isFSet es.toFinset) : isFormula (es.foldl Expr.or a) := by
  induction es generalizing a with
  | nil => exact ha
  | cons e es ih =>
      exact ih (or a e) (isFormula_or ha (hs e (by simp))) (fun q hq => hs q (by simp [hq]))

private def packOr (es : List Expr) (a : Expr) (ha : isFormula a)
    (hs : isFSet es.toFinset) {Γ : A.Context}
    (d : ProofTree Γ (insert (ofExpr a ha) (A.context es.toFinset hs))) :
    ProofTree Γ {ofExpr (es.foldl Expr.or a) (orFold_sorted es a ha hs)} := by
  induction es generalizing a with
  | nil => simpa using d
  | cons e es ih =>
      have he := hs e (by simp)
      have ht : isFSet es.toFinset := fun q hq => hs q (by simp [hq])
      exact ih (or a e) (isFormula_or ha he) ht (.rightOr a e ha he (by simpa using d))

private def proveAnd (es : List Expr) (a : Expr) (ha : isFormula a)
    (hs : isFSet es.toFinset) {Γ : A.Context} (d : ProofTree Γ {ofExpr a ha})
    (ds : ∀ e (he : e ∈ es), ProofTree Γ {ofExpr e (hs e (by simpa using he))}) :
    ProofTree Γ {ofExpr (es.foldl Expr.and a)
      (A.andFold_sorted es a ha (fun e he => hs e (by simpa using he)))} := by
  induction es generalizing a with
  | nil => exact d
  | cons e es ih =>
      have he := hs e (by simp)
      apply ih (and a e) (isFormula_and ha he) (fun q hq => hs q (by simp [hq]))
      · simpa using ProofTree.rightAnd (Δ := ∅) (Δ₁ := ∅) a e ha he d (ds e (by simp))
      · intro q hq; exact ds q (by simp [hq])

private def useOr (es : List Expr) (a : Expr) (ha : isFormula a)
    (hs : isFSet es.toFinset) {Δ : A.Context} (d : ProofTree {ofExpr a ha} Δ)
    (ds : ∀ e (he : e ∈ es), ProofTree {ofExpr e (hs e (by simpa using he))} Δ) :
    ProofTree {ofExpr (es.foldl Expr.or a) (orFold_sorted es a ha hs)} Δ := by
  induction es generalizing a with
  | nil => exact d
  | cons e es ih =>
      have he := hs e (by simp)
      apply ih (or a e) (isFormula_or ha he) (fun q hq => hs q (by simp [hq]))
      · simpa using ProofTree.leftOr (Γ := ∅) (Γ₁ := ∅) a e ha he d (ds e (by simp))
      · intro q hq; exact ds q (by simp [hq])

private def proveConjunction (Γ : Finset Expr) (hΓ : isFSet Γ) :
    ProofTree (A.context Γ hΓ) {ofExpr (conjunction Γ) (Ordered.conjunction_sorted hΓ)} := by
  have each (p : Expr) (hp : p ∈ Γ) : ProofTree (A.context Γ hΓ) {ofExpr p (hΓ p hp)} :=
    .weakening (.hypothesis _) (Finset.singleton_subset_iff.mpr ((mem_context hΓ _).mpr ⟨p, hp, rfl⟩)) (by rfl)
  cases he : Γ.toList with
  | nil =>
      have h : Γ = ∅ := by simpa using congrArg List.toFinset he
      subst Γ; simpa [conjunction, foldFormulas] using (ProofTree.rightTrue)
  | cons a es =>
      have hl : insert a es.toFinset = Γ := by simpa using (congrArg List.toFinset he).symm
      have ha := hΓ a (by rw [← hl]; simp)
      have hs : isFSet es.toFinset := fun q hq => hΓ q (by rw [← hl]; simp [hq])
      simpa [conjunction, he, foldFormulas] using proveAnd es a ha hs
        (each a (by rw [← hl]; simp)) (fun q hq => each q (by rw [← hl]; simp [hq]))

private def useDisjunction (Δ : Finset Expr) (hΔ : isFSet Δ) :
    ProofTree {ofExpr (disjunction Δ) (Ordered.disjunction_sorted hΔ)} (A.context Δ hΔ) := by
  have each (p : Expr) (hp : p ∈ Δ) : ProofTree {ofExpr p (hΔ p hp)} (A.context Δ hΔ) :=
    .weakening (.hypothesis _) (by rfl) (Finset.singleton_subset_iff.mpr ((mem_context hΔ _).mpr ⟨p, hp, rfl⟩))
  cases he : Δ.toList with
  | nil =>
      have h : Δ = ∅ := by simpa using congrArg List.toFinset he
      subst Δ; simpa [disjunction, foldFormulas] using (ProofTree.leftFalse)
  | cons a es =>
      have hl : insert a es.toFinset = Δ := by simpa using (congrArg List.toFinset he).symm
      have ha := hΔ a (by rw [← hl]; simp)
      have hs : isFSet es.toFinset := fun q hq => hΔ q (by rw [← hl]; simp [hq])
      simpa [disjunction, he, foldFormulas] using useOr es a ha hs
        (each a (by rw [← hl]; simp)) (fun q hq => each q (by rw [← hl]; simp [hq]))

def packSequent {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (d : ProofTree (A.context Γ hΓ) (A.context Δ hΔ)) :
    ProofTree ∅ {ofExpr (sequentToFormula Γ Δ) (Ordered.sequentToFormula_sorted hΓ hΔ)} := by
  have right : ProofTree (A.context Γ hΓ) {ofExpr (disjunction Δ) (Ordered.disjunction_sorted hΔ)} := by
    cases he : Δ.toList with
    | nil =>
        have h : Δ = ∅ := by simpa using congrArg List.toFinset he
        subst Δ
        exact .weakening d (by rfl) (by simp)
    | cons a es =>
        have hl : insert a es.toFinset = Δ := by simpa using (congrArg List.toFinset he).symm
        have hs : isFSet (insert a es.toFinset) := hl ▸ hΔ
        simpa [disjunction, he, foldFormulas] using packOr es a (hs a (by simp))
          (fun q hq => hs q (by simp [hq])) (by simpa [← hl] using d)
  by_cases h : Γ = ∅
  · simpa [sequentToFormula, h] using right
  · have left : ProofTree {ofExpr (conjunction Γ) (Ordered.conjunction_sorted hΓ)}
        {ofExpr (disjunction Δ) (Ordered.disjunction_sorted hΔ)} := by
      cases he : Γ.toList with
      | nil => exact False.elim (h (by simpa using congrArg List.toFinset he))
      | cons a es =>
          have hl : insert a es.toFinset = Γ := by simpa using (congrArg List.toFinset he).symm
          have hs : isFSet (insert a es.toFinset) := hl ▸ hΓ
          simpa [conjunction, he, foldFormulas] using packAnd es a (hs a (by simp))
            (fun q hq => hs q (by simp [hq])) (by simpa [← hl] using right)
    simpa [sequentToFormula, h] using ProofTree.rightImp (Γ := ∅) (Δ := ∅)
      (conjunction Γ) (disjunction Δ) (Ordered.conjunction_sorted hΓ) (Ordered.disjunction_sorted hΔ) left

def useSequentFormula {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    ProofTree (insert (ofExpr (sequentToFormula Γ Δ) (Ordered.sequentToFormula_sorted hΓ hΔ))
      (A.context Γ hΓ)) (A.context Δ hΔ) := by
  by_cases h : Γ = ∅
  · simpa [sequentToFormula, h] using useDisjunction Δ hΔ
  · simpa [sequentToFormula, h] using ProofTree.leftImp (Δ := ∅) (Γ₁ := ∅)
      (conjunction Γ) (disjunction Δ) (Ordered.conjunction_sorted hΓ) (Ordered.disjunction_sorted hΔ)
      (proveConjunction Γ hΓ) (useDisjunction Δ hΔ)

def restate {Γ Δ Γ' Δ' : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hΓ' : isFSet Γ') (hΔ' : isFSet Δ') (h : sequentLeq AlphaBetaEta Γ Δ Γ' Δ')
    (d : ProofTree (A.context Γ hΓ) (A.context Δ hΔ)) :
    ProofTree (A.context Γ' hΓ') (A.context Δ' hΔ') := by
  have he := (ofExpr_eq (Ordered.sequentToFormula_sorted hΓ hΔ) (Ordered.sequentToFormula_sorted hΓ' hΔ')).mpr h
  have packed := packSequent hΓ hΔ d
  rw [he] at packed
  simpa using ProofTree.cut (Γ := ∅) (Δ := ∅) _ packed (useSequentFormula hΓ' hΔ')

end Lisa.SCLambdaToPure.B
