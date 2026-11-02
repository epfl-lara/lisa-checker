import Lisa.LambdaFol.EliminateInstantiation.Equivalence
import Lisa.LambdaFol.ToPureFol.TranslateProof
import Lisa.LambdaFol.ToPureFol.PureFolToOrdered.Equivalence
import Lisa.LambdaFol.FromOrdered.TranslateProof

/-! Both directions of WithoutInstantiation-PureFol equivalence for first-order concluding sequents.
The reverse direction reuses PureFol -> Ordered -> LambdaFol -> WithoutInstantiation. -/
namespace Lisa.LambdaFol.WithoutInstantiation.Provable

theorem toPureFol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p)
    (d : WithoutInstantiation.Provable (LambdaFol.formulaSet Γ hΓ) (LambdaFol.formulaSet Δ hΔ)) :
    PureFol.Provable (PureFolTranslation.canonicalFormulaSet Γ) (PureFolTranslation.canonicalFormulaSet Δ) := by
  obtain ⟨d⟩ := d
  simpa only [FirstOrderAssignment.toPureFolFormulaClassSet_raw,
    PureFolTranslation.defaultAssignment_formulaSet hΓ hbΓ, PureFolTranslation.defaultAssignment_formulaSet hΔ hbΔ] using
    WithoutInstantiation.ProofTree.provable_toPureFol d _ FirstOrderAssignment.defaultAssignment_fixesConstants

theorem ofPureFol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p)
    (d : PureFol.Provable (PureFolTranslation.canonicalFormulaSet Γ) (PureFolTranslation.canonicalFormulaSet Δ)) :
    WithoutInstantiation.Provable (LambdaFol.formulaSet Γ hΓ) (LambdaFol.formulaSet Δ hΔ) := by
  obtain ⟨d⟩ := OrderedAlphaBetaEta.ofPureFol hΓ hΔ hbΓ hbΔ d
  exact ⟨LambdaFol.ProofTree.toWithoutInstantiation (LambdaFol.ProofTree.ofOrdered d hΓ hΔ)⟩

end Lisa.LambdaFol.WithoutInstantiation.Provable
