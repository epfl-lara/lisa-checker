import Lisa.LambdaFol.EliminateInstantiation.Equivalence
import Lisa.LambdaFol.ToPureFol.TranslateProof
import Lisa.LambdaFol.ToPureFol.PureFolToOrdered.Equivalence
import Lisa.LambdaFol.FromOrdered.TranslateProof

/-! Compose Ordered -> LambdaFol -> WithoutInstantiation -> PureFol and specialize to first-order conclusions. -/
namespace Lisa.LambdaFol

theorem ProofTree.provable_toPureFol {Γ Δ : Finset LambdaFol.Formula} (d : ProofTree Γ Δ)
    (R : FirstOrderAssignment) (hR : R.FixesConstants) :
    PureFol.Provable (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ) :=
  WithoutInstantiation.ProofTree.provable_toPureFol (ProofTree.toWithoutInstantiation d) R hR

end Lisa.LambdaFol

/-! The forward translation follows the paper's stages:
Ordered → LambdaFol (formula classes), LambdaFol → WithoutInstantiation (eliminate instantiation), WithoutInstantiation → PureFol
(default assignment, normalization, translation to PureFol). -/
namespace Lisa.LambdaFol

theorem ordered_toPureFol {Γ Δ : Finset Expr} (d : Ordered.ProofTree AlphaBetaEta Γ Δ)
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (R : FirstOrderAssignment) (hR : R.FixesConstants) :
    PureFol.Provable (R.toPureFolFormulaSet Γ) (R.toPureFolFormulaSet Δ) := by
  simpa only [FirstOrderAssignment.toPureFolFormulaClassSet_raw] using
    LambdaFol.ProofTree.provable_toPureFol (LambdaFol.ProofTree.ofOrdered d hΓ hΔ) R hR

end Lisa.LambdaFol

namespace Lisa.LambdaFol.OrderedAlphaBetaEta
open PureFolTranslation

/-- Translate an Ordered proof to PureFol when its conclusion satisfies the
first-order restrictions. Intermediate higher-order formulas remain permitted. -/
theorem toPureFol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p)
    (d : Provable Γ Δ) :
    PureFol.Provable (canonicalFormulaSet Γ) (canonicalFormulaSet Δ) := by
  obtain ⟨d⟩ := d
  simpa only [defaultAssignment_formulaSet hΓ hbΓ, defaultAssignment_formulaSet hΔ hbΔ] using
    ordered_toPureFol d hΓ hΔ _ FirstOrderAssignment.defaultAssignment_fixesConstants

end Lisa.LambdaFol.OrderedAlphaBetaEta
