import Lisa.Standard
import Lisa.Ordered

open Lisa
open Expr

namespace Bijection

def LeqContainedInStandard (leq : Order) : Prop :=
  ∀ {α β : Expr}, leq α β ->
    (isTerm α ∧ isTerm β ∧ α = β) ∨
    (isFormula α ∧ isFormula β ∧ Nonempty (Standard.ProofTree {α} {β}))

def SequentLeqClosedByStandard (leq : Order) : Type :=
  ∀ {Γ Δ Γ' Δ' : Finset Expr},
    isFSet Γ ->
    isFSet Δ ->
    isFSet Γ' ->
    isFSet Δ' ->
    sequentLeq leq Γ Δ Γ' Δ' ->
    Standard.ProofTree Γ Δ ->
    Standard.ProofTree Γ' Δ'

structure OrderCompatibleWithStandard (leq : Order) where
  reflexive : Reflexive leq
  pointwise : LeqContainedInStandard leq
  closed : SequentLeqClosedByStandard leq

@[simp]
private theorem isSame_refl {leq : Order} (href : Reflexive leq) (α : Expr) :
    isSame leq α α := by
  exact ⟨href α, href α⟩

private theorem setLeq_of_subset {leq : Order} (href : Reflexive leq)
    {Γ Ω : Finset Expr} (hsub : Γ ⊆ Ω) :
    setLeq leq Γ Ω := by
  intro φ hφ
  exact ⟨φ, hsub hφ, isSame_refl href φ⟩

private theorem sequentLeq_of_subset {leq : Order} (href : Reflexive leq)
    {Γ Δ Γ' Δ' : Finset Expr}
    (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') :
    sequentLeq leq Γ Δ Γ' Δ' := by
  dsimp [sequentLeq, setLeq]
  intro φ hφ
  rw [Finset.mem_union] at hφ
  rcases hφ with hφ | hφ
  · simp only [Finset.mem_image] at hφ
    rcases hφ with ⟨ψ, hψ, rfl⟩
    exact ⟨neg ψ, by
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨ψ, hΓ hψ, rfl⟩, isSame_refl href (neg ψ)⟩
  · exact ⟨φ, by simp [hΔ hφ], isSame_refl href φ⟩

def standardToOrdered {leq Γ Δ} (href : Reflexive leq) :
    Standard.ProofTree Γ Δ ->
    Ordered.ProofTree leq Γ Δ
  | .weakening hΓ hΔ hΓ' hΔ' pf hsubΓ hsubΔ =>
      Ordered.ProofTree.weakening hΓ hΔ hΓ' hΔ'
        (standardToOrdered href pf)
        (sequentLeq_of_subset href hsubΓ hsubΔ)
  | .hypothesis φ hφ =>
      Ordered.ProofTree.hypothesis φ hφ
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      Ordered.ProofTree.cut φ hΓ hΔ hΩ hΞ hφ
        (standardToOrdered href pf₁)
        (standardToOrdered href pf₂)
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      Ordered.ProofTree.leftAnd φ ψ hΓ hΔ hφ hψ
        (standardToOrdered href pf)
  | .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Ordered.ProofTree.leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (standardToOrdered href pf₁)
        (standardToOrdered href pf₂)
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Ordered.ProofTree.leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (standardToOrdered href pf₁)
        (standardToOrdered href pf₂)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      Ordered.ProofTree.leftIff φ ψ hΓ hΔ hφ hψ
        (standardToOrdered href pf)
  | .leftNot φ hΓ hΔ hφ pf =>
      Ordered.ProofTree.leftNot φ hΓ hΔ hφ
        (standardToOrdered href pf)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      Ordered.ProofTree.leftForall x φ t hΓ hΔ hx hφ ht
        (standardToOrdered href pf)
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      Ordered.ProofTree.leftExists x φ hΓ hΔ hx hφ
        (standardToOrdered href pf)
        hfree
  | .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Ordered.ProofTree.rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (standardToOrdered href pf₁)
        (standardToOrdered href pf₂)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      Ordered.ProofTree.rightOr φ ψ hΓ hΔ hφ hψ
        (standardToOrdered href pf)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      Ordered.ProofTree.rightImp φ ψ hΓ hΔ hφ hψ
        (standardToOrdered href pf)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Ordered.ProofTree.rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (standardToOrdered href pf₁)
        (standardToOrdered href pf₂)
  | .rightNot φ hΓ hΔ hφ pf =>
      Ordered.ProofTree.rightNot φ hΓ hΔ hφ
        (standardToOrdered href pf)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      Ordered.ProofTree.rightForall x φ hΓ hΔ hx hφ
        (standardToOrdered href pf)
        hfree
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      Ordered.ProofTree.rightExists x φ t hΓ hΔ hx hφ ht
        (standardToOrdered href pf)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      Ordered.ProofTree.rightEpsilon x φ t hΓ hΔ hx hφ ht
        (standardToOrdered href pf)
  | .leftRefl t hΓ hΔ ht pf =>
      Ordered.ProofTree.leftRefl t hΓ hΔ ht
        (standardToOrdered href pf)
  | .rightRefl t ht =>
      Ordered.ProofTree.rightRefl t ht
  | .leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      Ordered.ProofTree.leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift
        (standardToOrdered href pf)
  | .rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      Ordered.ProofTree.rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift
        (standardToOrdered href pf)
  | .instSchema σ hΓ hΔ hσ pf =>
      Ordered.ProofTree.instSchema σ hΓ hΔ hσ
        (standardToOrdered href pf)

def orderedToStandard {leq Γ Δ}
    (hclosed : SequentLeqClosedByStandard leq) :
    Ordered.ProofTree leq Γ Δ ->
    Standard.ProofTree Γ Δ
  | .restate hΓ hΔ hΓ' hΔ' pf hle₁ _ =>
      hclosed hΓ hΔ hΓ' hΔ' hle₁
        (orderedToStandard hclosed pf)
  | .weakening hΓ hΔ hΓ' hΔ' pf hle =>
      hclosed hΓ hΔ hΓ' hΔ' hle
        (orderedToStandard hclosed pf)
  | .hypothesis φ hφ =>
      Standard.ProofTree.hypothesis φ hφ
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      Standard.ProofTree.cut φ hΓ hΔ hΩ hΞ hφ
        (orderedToStandard hclosed pf₁)
        (orderedToStandard hclosed pf₂)
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      Standard.ProofTree.leftAnd φ ψ hΓ hΔ hφ hψ
        (orderedToStandard hclosed pf)
  | .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Standard.ProofTree.leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (orderedToStandard hclosed pf₁)
        (orderedToStandard hclosed pf₂)
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Standard.ProofTree.leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (orderedToStandard hclosed pf₁)
        (orderedToStandard hclosed pf₂)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      Standard.ProofTree.leftIff φ ψ hΓ hΔ hφ hψ
        (orderedToStandard hclosed pf)
  | .leftNot φ hΓ hΔ hφ pf =>
      Standard.ProofTree.leftNot φ hΓ hΔ hφ
        (orderedToStandard hclosed pf)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      Standard.ProofTree.leftForall x φ t hΓ hΔ hx hφ ht
        (orderedToStandard hclosed pf)
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      Standard.ProofTree.leftExists x φ hΓ hΔ hx hφ
        (orderedToStandard hclosed pf)
        hfree
  | .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Standard.ProofTree.rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (orderedToStandard hclosed pf₁)
        (orderedToStandard hclosed pf₂)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      Standard.ProofTree.rightOr φ ψ hΓ hΔ hφ hψ
        (orderedToStandard hclosed pf)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      Standard.ProofTree.rightImp φ ψ hΓ hΔ hφ hψ
        (orderedToStandard hclosed pf)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Standard.ProofTree.rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (orderedToStandard hclosed pf₁)
        (orderedToStandard hclosed pf₂)
  | .rightNot φ hΓ hΔ hφ pf =>
      Standard.ProofTree.rightNot φ hΓ hΔ hφ
        (orderedToStandard hclosed pf)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      Standard.ProofTree.rightForall x φ hΓ hΔ hx hφ
        (orderedToStandard hclosed pf)
        hfree
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      Standard.ProofTree.rightExists x φ t hΓ hΔ hx hφ ht
        (orderedToStandard hclosed pf)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      Standard.ProofTree.rightEpsilon x φ t hΓ hΔ hx hφ ht
        (orderedToStandard hclosed pf)
  | .leftRefl t hΓ hΔ ht pf =>
      Standard.ProofTree.leftRefl t hΓ hΔ ht
        (orderedToStandard hclosed pf)
  | .rightRefl t ht =>
      Standard.ProofTree.rightRefl t ht
  | .leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      Standard.ProofTree.leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift
        (orderedToStandard hclosed pf)
  | .rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      Standard.ProofTree.rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift
        (orderedToStandard hclosed pf)
  | .instSchema σ hΓ hΔ hσ pf =>
      Standard.ProofTree.instSchema σ hΓ hΔ hσ
        (orderedToStandard hclosed pf)

theorem standard_eq_ordered (leq : Order) (Γ Δ : Finset Expr)
    (href : Reflexive leq)
    (hclosed : SequentLeqClosedByStandard leq) :
    Nonempty (Standard.ProofTree Γ Δ) ↔
    Nonempty (Ordered.ProofTree leq Γ Δ) := by
  constructor <;> intro ⟨pf⟩
  · exact ⟨standardToOrdered href pf⟩
  · exact ⟨orderedToStandard hclosed pf⟩

theorem standard_eq_ordered_of_compatible (leq : Order) (Γ Δ : Finset Expr)
    (hcompat : OrderCompatibleWithStandard leq) :
    Nonempty (Standard.ProofTree Γ Δ) ↔
    Nonempty (Ordered.ProofTree leq Γ Δ) := by
  exact standard_eq_ordered leq Γ Δ hcompat.reflexive hcompat.closed

end Bijection
