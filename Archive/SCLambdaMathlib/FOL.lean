import Lisa.SCLambdaToPure.BToPure
import Lisa.SCLambdaToPure.MathlibCalculus

/-! A and B with the independent target in epsilon-disabled mode.
The syntax bridge preserves the established A/B construction and its connective
encodings, and transports complete derivations in both directions. -/
namespace Lisa.SCLambdaToPure
noncomputable local instance : DecidableEq (PureSyntax.Formula Readback.language .fol) := Classical.decEq _

namespace FOL
open Readback (language)

noncomputable def context (Γ : A.Context) : PureSyntax.Context language .fol :=
  MathlibSyntax.ofContext (Translation.context Γ)

noncomputable def canonicalContext (Γ : Finset Expr) (hΓ : isFSet Γ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) : PureSyntax.Context language .fol :=
  MathlibSyntax.ofContext (Translation.canonicalContext Γ hΓ hbΓ)

/-- Transport A proofs into the common first-order syntax, with epsilon disabled. -/
noncomputable def fromA {Γ Δ : A.Context} (d : A.ProofTree ∅ Γ Δ) :
    PureSyntax.ProofTree ∅ (context Γ) (context Δ) :=
  MathlibSyntax.ofProof (Translation.toPure d)

/-- B's instantiation elimination is unchanged. -/
noncomputable def fromB {Γ Δ : A.Context} (d : B.ProofTree ∅ Γ Δ) :
    PureSyntax.ProofTree ∅ (context Γ) (context Δ) := fromA (B.toA d)

end FOL

theorem a_iff_pure_fol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    A.Provable ∅ (A.context Γ hΓ) (A.context Δ hΔ) ↔
      PureSyntax.Provable ∅ (FOL.canonicalContext Γ hΓ hbΓ) (FOL.canonicalContext Δ hΔ hbΔ) :=
  (a_iff_pure hΓ hΔ hbΓ hbΔ).trans MathlibSyntax.provable_iff

theorem b_iff_pure_fol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    B.Provable ∅ (A.context Γ hΓ) (A.context Δ hΔ) ↔
      PureSyntax.Provable ∅ (FOL.canonicalContext Γ hΓ hbΓ) (FOL.canonicalContext Δ hΔ hbΔ) :=
  b_iff_a.trans (a_iff_pure_fol hΓ hΔ hbΓ hbΔ)

end Lisa.SCLambdaToPure
