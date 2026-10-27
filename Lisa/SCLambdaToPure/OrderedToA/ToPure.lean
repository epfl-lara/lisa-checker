import Lisa.SCLambdaToPure.AToPure.Derivation
import Lisa.SCLambdaToPure.AToPure.Reverse.Equivalence
import Lisa.SCLambdaToPure.OrderedToA.ToB

/-! Compose Ordered -> B -> A -> Pure and specialize to first-order conclusions. -/
namespace Lisa.SCLambdaToPure.B

theorem toPure {Γ Δ : A.Context} (d : ProofTree Γ Δ)
    (R : Syntactic.Assignment) (hR : R.FixesConstants) :
    Pure.Provable (R.classContext Γ) (R.classContext Δ) :=
  A.toPure (toA d) R hR

end Lisa.SCLambdaToPure.B

/-! The forward translation follows the paper's stages:
Ordered → B (formula classes), B → A (eliminate instantiation), A → Pure
(grounding, normalization, readback). No direct Ordered-to-Pure induction remains. -/
namespace Lisa.SCLambdaToPure.Syntactic

theorem ordered_toPure {Γ Δ : Finset Expr} (d : Ordered.ProofTree AlphaBetaEta Γ Δ)
    (hΓ : isFSet Γ) (hΔ : isFSet Δ) (R : Assignment) (hR : R.FixesConstants) :
    Pure.Provable (R.context Γ) (R.context Δ) := by
  simpa only [Assignment.classContext_raw] using
    B.toPure (B.ofOrdered d hΓ hΔ) R hR

end Lisa.SCLambdaToPure.Syntactic


namespace Lisa.SCLambdaToPure.OrderedReduction
open Readback

/-- Forward transport of complete source derivations, with first-order readback
of the conclusion. All intermediate higher-order formulas remain permitted. -/
theorem toPure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p)
    (d : Provable Γ Δ) :
    Pure.Provable (canonicalContext Γ) (canonicalContext Δ) := by
  obtain ⟨d⟩ := d
  simpa only [grounding_context hΓ hbΓ, grounding_context hΔ hbΔ] using
    Syntactic.ordered_toPure d hΓ hΔ _ Syntactic.Assignment.grounding_fixesConstants

end Lisa.SCLambdaToPure.OrderedReduction
