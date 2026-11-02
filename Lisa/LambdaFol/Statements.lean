import Lisa.LambdaFol.ToPureFol.Equivalence
import Lisa.LambdaFol.ToPureFol.FromOrdered

/-!
# Equivalence of Ordered alpha-beta-eta, WithoutInstantiation, and PureFol

The calculi are defined in `ProofSystem.lean`, `WithoutInstantiation.lean`,
and `PureFol.lean`, using the shared formula classes in `Syntax.lean`.
The supporting proofs follow Ordered → LambdaFol → WithoutInstantiation → PureFol,
in `FromOrdered/`, `EliminateInstantiation/`, and `ToPureFol/` respectively.

The first-order restriction applies only to the concluding sequent, not to
intermediate formulas. All systems retain epsilon.
-/

namespace Lisa.LambdaFol

/-- WithoutInstantiation and the canonical first-order sequent are equiprovable. -/
theorem withoutInstantiation_iff_pureFol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p) :
    WithoutInstantiation.Provable (LambdaFol.formulaSet Γ hΓ) (LambdaFol.formulaSet Δ hΔ) ↔
      PureFol.Provable (PureFolTranslation.canonicalFormulaSet Γ) (PureFolTranslation.canonicalFormulaSet Δ) :=
  ⟨WithoutInstantiation.Provable.toPureFol hΓ hΔ hbΓ hbΔ, WithoutInstantiation.Provable.ofPureFol hΓ hΔ hbΓ hbΔ⟩

theorem lambdaFol_iff_pureFol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p) :
    LambdaFol.Provable (LambdaFol.formulaSet Γ hΓ) (LambdaFol.formulaSet Δ hΔ) ↔
      PureFol.Provable (PureFolTranslation.canonicalFormulaSet Γ) (PureFolTranslation.canonicalFormulaSet Δ) :=
  lambdaFol_iff_withoutInstantiation.trans (withoutInstantiation_iff_pureFol hΓ hΔ hbΓ hbΔ)

/-- Ordered alpha-beta-eta and the canonical first-order sequent are equiprovable. -/
theorem ordered_iff_pureFol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p) :
    OrderedAlphaBetaEta.Provable Γ Δ ↔ PureFol.Provable
      (PureFolTranslation.canonicalFormulaSet Γ) (PureFolTranslation.canonicalFormulaSet Δ) :=
  ⟨OrderedAlphaBetaEta.toPureFol hΓ hΔ hbΓ hbΔ, OrderedAlphaBetaEta.ofPureFol hΓ hΔ hbΓ hbΔ⟩

/-- Ordered alpha-beta-eta and WithoutInstantiation prove the same sequents satisfying the first-order restrictions. -/
theorem ordered_iff_withoutInstantiation {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p) :
    OrderedAlphaBetaEta.Provable Γ Δ ↔ WithoutInstantiation.Provable (LambdaFol.formulaSet Γ hΓ) (LambdaFol.formulaSet Δ hΔ) :=
  (ordered_iff_pureFol hΓ hΔ hbΓ hbΔ).trans (withoutInstantiation_iff_pureFol hΓ hΔ hbΓ hbΔ).symm

end Lisa.LambdaFol
