import Lisa.SCLambdaToPure.AToPure.Derivation
import Lisa.SCLambdaToPure.AToPure.Reverse.Equivalence
import Lisa.SCLambdaToPure.OrderedToA.ToB

/-! Both directions of A-Pure equivalence for first-order concluding sequents.
The reverse direction reuses Pure -> Ordered -> B -> A. -/
namespace Lisa.SCLambdaToPure.A.Provable

theorem toPure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p)
    (d : A.Provable (A.context Γ hΓ) (A.context Δ hΔ)) :
    Pure.Provable (Readback.canonicalContext Γ) (Readback.canonicalContext Δ) := by
  obtain ⟨d⟩ := d
  simpa only [Syntactic.Assignment.classContext_raw,
    Readback.grounding_context hΓ hbΓ, Readback.grounding_context hΔ hbΔ] using
    A.toPure d _ Syntactic.Assignment.grounding_fixesConstants

theorem ofPure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p)
    (d : Pure.Provable (Readback.canonicalContext Γ) (Readback.canonicalContext Δ)) :
    A.Provable (A.context Γ hΓ) (A.context Δ hΔ) := by
  obtain ⟨d⟩ := OrderedReduction.ofPure hΓ hΔ hbΓ hbΔ d
  exact ⟨B.toA (B.ofOrdered d hΓ hΔ)⟩

end Lisa.SCLambdaToPure.A.Provable
