import Lisa.Standard
import Lisa.Ordered

open Lisa
open Expr

namespace StandardOrdered

/-- Supply an admissibility proof for whole-sequent weakening in Standard.

This is a separate proof obligation, not a consequence of the ortholattice laws.
In particular, those laws interpret literal truth and falsity, whereas Standard
has no introduction rule for the truth constant.
-/
def SequentLeqClosedByStandard (leq : Order) : Type :=
  ∀ {Γ Δ Γ' Δ' : Finset Expr},
    isFSet Γ →
    isFSet Δ →
    isFSet Γ' →
    isFSet Δ' →
    sequentLeq leq Γ Δ Γ' Δ' →
    Standard.ProofTree Γ Δ →
    Standard.ProofTree Γ' Δ'

@[simp] private theorem isSame_refl {leq : Order} [Std.Refl leq] (α : Expr) :
    isSame leq α α := ⟨OrderLaws.self_le α, OrderLaws.self_le α⟩

private theorem sequentLeq_of_subset {leq : Order} [Std.Refl leq] [SequentWeakening leq]
    {Γ Δ Γ' Δ' : Finset Expr}
    (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') :
    sequentLeq leq Γ Δ Γ' Δ' :=
  SequentWeakening.weaken
    (fun φ hφ => ⟨φ, hΓ hφ, isSame_refl φ⟩)
    (fun φ hφ => ⟨φ, hΔ hφ, isSame_refl φ⟩)

def standardToOrdered {leq Γ Δ} [Std.Refl leq] [SequentWeakening leq] :
    Standard.ProofTree Γ Δ →
    Ordered.ProofTree leq Γ Δ
  | .weakening hΓ hΔ hΓ' hΔ' pf hsubΓ hsubΔ =>
      .weakening hΓ hΔ hΓ' hΔ' (standardToOrdered pf)
        (sequentLeq_of_subset hsubΓ hsubΔ)
  | .hypothesis φ hφ =>
      .hypothesis φ hφ
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      .cut φ hΓ hΔ hΩ hΞ hφ (standardToOrdered pf₁) (standardToOrdered pf₂)
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      .leftAnd φ ψ hΓ hΔ hφ hψ (standardToOrdered pf)
  | .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ (standardToOrdered pf₁) (standardToOrdered pf₂)
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ (standardToOrdered pf₁) (standardToOrdered pf₂)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      .leftIff φ ψ hΓ hΔ hφ hψ (standardToOrdered pf)
  | .leftNot φ hΓ hΔ hφ pf =>
      .leftNot φ hΓ hΔ hφ (standardToOrdered pf)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      .leftForall x φ t hΓ hΔ hx hφ ht (standardToOrdered pf)
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      .leftExists x φ hΓ hΔ hx hφ (standardToOrdered pf) hfree
  | .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ (standardToOrdered pf₁) (standardToOrdered pf₂)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      .rightOr φ ψ hΓ hΔ hφ hψ (standardToOrdered pf)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      .rightImp φ ψ hΓ hΔ hφ hψ (standardToOrdered pf)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ (standardToOrdered pf₁) (standardToOrdered pf₂)
  | .rightNot φ hΓ hΔ hφ pf =>
      .rightNot φ hΓ hΔ hφ (standardToOrdered pf)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      .rightForall x φ hΓ hΔ hx hφ (standardToOrdered pf) hfree
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      .rightExists x φ t hΓ hΔ hx hφ ht (standardToOrdered pf)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      .rightEpsilon x φ t hΓ hΔ hx hφ ht (standardToOrdered pf)
  | .leftRefl t hΓ hΔ ht pf =>
      .leftRefl t hΓ hΔ ht (standardToOrdered pf)
  | .rightRefl t ht =>
      .rightRefl t ht
  | .leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      .leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift (standardToOrdered pf)
  | .rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      .rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift (standardToOrdered pf)
  | .instSchema σ hΓ hΔ hσ pf =>
      .instSchema σ hΓ hΔ hσ (standardToOrdered pf)

def orderedToStandard {leq Γ Δ}
    (hclosed : SequentLeqClosedByStandard leq) :
    Ordered.ProofTree leq Γ Δ →
    Standard.ProofTree Γ Δ
  | .restate hΓ hΔ hΓ' hΔ' pf hle₁ _ =>
      hclosed hΓ hΔ hΓ' hΔ' hle₁ (orderedToStandard hclosed pf)
  | .weakening hΓ hΔ hΓ' hΔ' pf hle =>
      hclosed hΓ hΔ hΓ' hΔ' hle (orderedToStandard hclosed pf)
  | .hypothesis φ hφ =>
      .hypothesis φ hφ
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      .cut φ hΓ hΔ hΩ hΞ hφ (orderedToStandard hclosed pf₁) (orderedToStandard hclosed pf₂)
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      .leftAnd φ ψ hΓ hΔ hφ hψ (orderedToStandard hclosed pf)
  | .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ (orderedToStandard hclosed pf₁) (orderedToStandard hclosed pf₂)
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ (orderedToStandard hclosed pf₁) (orderedToStandard hclosed pf₂)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      .leftIff φ ψ hΓ hΔ hφ hψ (orderedToStandard hclosed pf)
  | .leftNot φ hΓ hΔ hφ pf =>
      .leftNot φ hΓ hΔ hφ (orderedToStandard hclosed pf)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      .leftForall x φ t hΓ hΔ hx hφ ht (orderedToStandard hclosed pf)
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      .leftExists x φ hΓ hΔ hx hφ (orderedToStandard hclosed pf) hfree
  | .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (orderedToStandard hclosed pf₁) (orderedToStandard hclosed pf₂)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      .rightOr φ ψ hΓ hΔ hφ hψ (orderedToStandard hclosed pf)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      .rightImp φ ψ hΓ hΔ hφ hψ (orderedToStandard hclosed pf)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (orderedToStandard hclosed pf₁) (orderedToStandard hclosed pf₂)
  | .rightNot φ hΓ hΔ hφ pf =>
      .rightNot φ hΓ hΔ hφ (orderedToStandard hclosed pf)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      .rightForall x φ hΓ hΔ hx hφ (orderedToStandard hclosed pf) hfree
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      .rightExists x φ t hΓ hΔ hx hφ ht (orderedToStandard hclosed pf)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      .rightEpsilon x φ t hΓ hΔ hx hφ ht (orderedToStandard hclosed pf)
  | .leftRefl t hΓ hΔ ht pf =>
      .leftRefl t hΓ hΔ ht (orderedToStandard hclosed pf)
  | .rightRefl t ht =>
      .rightRefl t ht
  | .leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      .leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift (orderedToStandard hclosed pf)
  | .rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      .rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift (orderedToStandard hclosed pf)
  | .instSchema σ hΓ hΔ hσ pf =>
      .instSchema σ hΓ hΔ hσ (orderedToStandard hclosed pf)

theorem standard_eq_ordered (leq : Order) [Std.Refl leq] [SequentWeakening leq]
    (Γ Δ : Finset Expr)
    (hclosed : SequentLeqClosedByStandard leq) :
    Nonempty (Standard.ProofTree Γ Δ) ↔
    Nonempty (Ordered.ProofTree leq Γ Δ) := by
  constructor <;> intro ⟨pf⟩
  · exact ⟨standardToOrdered pf⟩
  · exact ⟨orderedToStandard hclosed pf⟩

end StandardOrdered
