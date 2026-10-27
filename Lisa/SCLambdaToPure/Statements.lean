import Lisa.SCLambdaToPure.AToPure.Equivalence
import Lisa.SCLambdaToPure.OrderedToA.ToPure

/-!
# Equivalence of Ordered alpha-beta-eta, A, and Pure

`Pure.lean` and `A.lean` define the proof systems. Supporting proofs live in
`AToPure/` and `OrderedToA/`; this file collects the concluding equivalences.
The forward proof follows Ordered -> B -> A -> Pure, retaining B as the calculus
modulo alpha-beta-eta with instantiation and without primitive restatement.

The first-order restriction applies only to the concluding sequent, not to
intermediate formulas. All systems retain epsilon.
-/

namespace Lisa.SCLambdaToPure

/-- A and the canonical first-order sequent are equiprovable. -/
theorem a_iff_pure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    A.Provable (A.context Γ hΓ) (A.context Δ hΔ) ↔
      Pure.Provable (Readback.canonicalContext Γ) (Readback.canonicalContext Δ) :=
  ⟨A.Provable.toPure hΓ hΔ hbΓ hbΔ, A.Provable.ofPure hΓ hΔ hbΓ hbΔ⟩

theorem b_iff_pure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    B.Provable (A.context Γ hΓ) (A.context Δ hΔ) ↔
      Pure.Provable (Readback.canonicalContext Γ) (Readback.canonicalContext Δ) :=
  b_iff_a.trans (a_iff_pure hΓ hΔ hbΓ hbΔ)


/-- Ordered alpha-beta-eta and the canonical first-order sequent are equiprovable. -/
theorem ordered_iff_pure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    OrderedReduction.Provable Γ Δ ↔ Pure.Provable
      (Readback.canonicalContext Γ) (Readback.canonicalContext Δ) :=
  ⟨OrderedReduction.toPure hΓ hΔ hbΓ hbΔ, OrderedReduction.ofPure hΓ hΔ hbΓ hbΔ⟩

/-- Ordered alpha-beta-eta and A prove the same first-order boundary sequents. -/
theorem ordered_iff_a {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    OrderedReduction.Provable Γ Δ ↔ A.Provable (A.context Γ hΓ) (A.context Δ hΔ) :=
  (ordered_iff_pure hΓ hΔ hbΓ hbΔ).trans (a_iff_pure hΓ hΔ hbΓ hbΔ).symm

end Lisa.SCLambdaToPure
