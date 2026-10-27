import Lisa.SCLambdaToPure.SyntacticTranslation
import Lisa.SCLambdaToPure.PureEncoding
import Lisa.OrderedEncoding

/-! Whole-sequent alpha-beta-eta restatement transports through the actual
sequent encoding. No per-formula matching premise is introduced. -/
namespace Lisa.SCLambdaToPure.Syntactic
namespace Assignment
variable {R : Assignment}

private theorem formula_fold (op : Expr → Expr → Expr)
    (bop : PureSyntax.Formula Readback.language .epsilon →
      PureSyntax.Formula Readback.language .epsilon → PureSyntax.Formula Readback.language .epsilon)
    (sorted : ∀ {p q}, isFormula p → isFormula q → isFormula (op p q))
    (commutes : ∀ p q, isFormula p → isFormula q → R.formula (op p q) = bop (R.formula p) (R.formula q))
    (xs : List Expr) (a : Expr) (ha : isFormula a) (hx : ∀ x ∈ xs, isFormula x) :
    R.formula (xs.foldl op a) = (xs.map R.formula).foldl bop (R.formula a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (op a b) (sorted ha (hx b (by simp))) (fun x h => hx x (by simp [h])),
        commutes a b ha (hx b (by simp))]

theorem formula_conjunction (hR : R.Logical) {Γ : Finset Expr} (hΓ : isFSet Γ) :
    R.formula (conjunction Γ) = PureSyntax.conjoin (Γ.toList.map R.formula) := by
  have hs : ∀ x ∈ Γ.toList, isFormula x := by simpa using hΓ
  unfold conjunction
  generalize Γ.toList = xs at hs ⊢
  cases xs with
  | nil => exact R.formula_top hR
  | cons a xs =>
      exact formula_fold Expr.and PureSyntax.BFormula.and isFormula_and
        (fun _ _ hp hq => R.formula_and hR hp hq) xs a (hs a (by simp)) (fun x hx => hs x (by simp [hx]))

theorem formula_disjunction (hR : R.Logical) {Δ : Finset Expr} (hΔ : isFSet Δ) :
    R.formula (disjunction Δ) = PureSyntax.disjoin (Δ.toList.map R.formula) := by
  have hs : ∀ x ∈ Δ.toList, isFormula x := by simpa using hΔ
  unfold disjunction
  generalize Δ.toList = xs at hs ⊢
  cases xs with
  | nil => exact R.formula_bot hR
  | cons a xs =>
      exact formula_fold Expr.or PureSyntax.BFormula.or isFormula_or
        (fun _ _ hp hq => R.formula_or hR hp hq) xs a (hs a (by simp)) (fun x hx => hs x (by simp [hx]))

@[simp] theorem context_list (R : Assignment) (Γ : Finset Expr) :
    (Γ.toList.map R.formula).toFinset = R.context Γ := by
  ext p
  simp [context]

theorem encode (R : Assignment) (hR : R.Logical) {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (d : PureSyntax.Provable ∅ (R.context Γ) (R.context Δ)) :
    PureSyntax.Provable ∅ ∅ {R.formula (sequentToFormula Γ Δ)} := by
  obtain ⟨d⟩ := d
  by_cases he : Γ = ∅
  · subst Γ
    have h := PureSyntax.ProofTree.disjoin_right (T := ∅) (Γ := ∅) (Δ := ∅)
      (Δ.toList.map R.formula) (by simpa using d)
    exact ⟨by simpa [sequentToFormula, R.formula_disjunction hR hΔ] using h⟩
  · have h := PureSyntax.ProofTree.encode (T := ∅) (Γ.toList.map R.formula) (Δ.toList.map R.formula)
      (by simpa using d)
    exact ⟨by simpa only [sequentToFormula, if_neg he,
      R.formula_imp hR (Ordered.conjunction_sorted hΓ) (Ordered.disjunction_sorted hΔ),
      R.formula_conjunction hR hΓ, R.formula_disjunction hR hΔ] using h⟩

theorem decode (R : Assignment) (hR : R.Logical) {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (d : PureSyntax.Provable ∅ ∅ {R.formula (sequentToFormula Γ Δ)}) :
    PureSyntax.Provable ∅ (R.context Γ) (R.context Δ) := by
  obtain ⟨d⟩ := d
  by_cases he : Γ = ∅
  · subst Γ
    have proj := PureSyntax.ProofTree.disjoin_left (T := ∅) (Δ.toList.map R.formula)
    have d' : PureSyntax.ProofTree (∅ : PureSyntax.Theory Readback.language .epsilon) ∅
        {PureSyntax.disjoin (Δ.toList.map R.formula)} := by
      simpa [sequentToFormula, R.formula_disjunction hR hΔ] using d
    refine ⟨?_⟩
    simpa using PureSyntax.ProofTree.cut (Γ := ∅) (Δ := ∅) (Θ := ∅)
      (PureSyntax.disjoin (Δ.toList.map R.formula)) d' proj
  · have d' : PureSyntax.ProofTree (∅ : PureSyntax.Theory Readback.language .epsilon) ∅
        {.imp (PureSyntax.conjoin (Γ.toList.map R.formula)) (PureSyntax.disjoin (Δ.toList.map R.formula))} := by
      simpa only [sequentToFormula, if_neg he,
        R.formula_imp hR (Ordered.conjunction_sorted hΓ) (Ordered.disjunction_sorted hΔ),
        R.formula_conjunction hR hΓ, R.formula_disjunction hR hΔ] using d
    exact ⟨by simpa using PureSyntax.ProofTree.decode (Γ.toList.map R.formula) (Δ.toList.map R.formula) d'⟩

theorem restate (R : Assignment) (hR : R.Logical) {Γ Δ Γ' Δ' : Finset Expr}
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (hΓ' : isFSet Γ') (hΔ' : isFSet Δ')
    (h : sequentLeq AlphaBetaEta Γ Δ Γ' Δ')
    (d : PureSyntax.Provable ∅ (R.context Γ) (R.context Δ)) :
    PureSyntax.Provable ∅ (R.context Γ') (R.context Δ') := by
  have encoded := R.encode hR hΓ hΔ d
  rw [R.formula_equiv h (Ordered.sequentToFormula_sorted hΓ hΔ)] at encoded
  exact R.decode hR hΓ' hΔ' encoded

end Assignment
end Lisa.SCLambdaToPure.Syntactic
