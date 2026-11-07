import Lisa.LambdaFol.FirstOrder
import Lisa.LambdaFol.Translation
import Lisa.LambdaFol.ToPureFol.TranslateNamedExpressions
import Lisa.LambdaFol.ToPureFol.DefaultAssignment

/-! The concluding formulas to which the equivalence applies, and their
canonical first-order translation. Epsilon remains in the first-order language.
Intermediate formulas of a derivation need not satisfy these restrictions. -/
namespace Lisa.LambdaFol

namespace PureFolTranslation

theorem canonicalFormula_spec {p : Expr} (hp : isFormula p) (hb : FirstOrderCompatible p) :
    fromExprFormula? p = some (canonicalFormula p) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (fromExprFormula_isSome hp hb.1 hb.2)
  simp [canonicalFormula, hq]

theorem defaultAssignment_formula {p : Expr} (hp : isFormula p) (hb : FirstOrderCompatible p) :
    FirstOrderAssignment.defaultAssignment.toPureFolFormula p = canonicalFormula p := by
  obtain ⟨e, he⟩ := AlphaBetaEtaNormalization.Algorithm.interpretNamed_sorted hp AlphaBetaEtaNormalization.Algorithm.Names.free
  let a : FirstOrderCompatibleExpr prop :=
    ⟨e, FirstOrderShape.compatible_of_interpretNamed he hb.1 hb.2, AlphaBetaEtaNormalization.Algorithm.subst_of_interpretNamed he⟩
  have hf : FirstOrderAssignment.defaultAssignment.applyExpr p hp = a := by
    rw [FirstOrderAssignment.applyExpr_of_named _ p hp he]
    exact FirstOrderAssignment.defaultAssignment_apply a
  rw [FirstOrderAssignment.toPureFolFormula_of_sorted _ p hp, hf]
  have hr : fromExprFormula? p = some a.toPureFolFormula := by
    simpa [fromExprFormula?, PureFolTranslation.normalizeExpr?, he, a] using a.toPureFolFormula_spec
  exact Option.some.inj (hr.symm.trans (canonicalFormula_spec hp hb))

theorem defaultAssignment_formulaSet {Γ : Finset Expr} (hΓ : isFSet Γ)
    (hb : ∀ p ∈ Γ, FirstOrderCompatible p) :
    FirstOrderAssignment.defaultAssignment.toPureFolFormulaSet Γ = canonicalFormulaSet Γ := by
  apply Finset.image_congr
  intro p hp
  exact defaultAssignment_formula (hΓ p hp) (hb p hp)

end PureFolTranslation

end Lisa.LambdaFol
