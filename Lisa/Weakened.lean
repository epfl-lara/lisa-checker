import Lisa.Syntax
import Lisa.Standard

/-
  This module defined the order-weakened λFOL proof system as used by the Lisa
  proof checker.
-/

open Lisa

@[simp]
def ordContains (leq : Order) (α : Expr) (Γ : Finset Expr) : Prop :=
  ∃ β ∈ Γ, leq α β

@[simp]
def isSame (leq : Order) (α β : Expr) : Prop :=
  leq α β ∧ leq β α

/-- A sequent annotated with one additional value. Used as premise carrying
  proof step information for multi-premise steps -/
structure AnnotatedSequent (α : Type) where
  pre : Finset Expr
  post : Finset Expr
  val : α
deriving DecidableEq, Inhabited

namespace Weakened

open Expr

inductive ProofTree (leq : Order) : (Γ Δ : Finset Expr) -> Type where
  -- ordering rules
  -- unchanged from the standard system
  | restate {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Γ' ->
      isFSet Δ' ->
      ProofTree leq Γ Δ ->
      sequentLeq leq Γ Δ Γ' Δ' ->
      sequentLeq leq Γ' Δ' Γ Δ ->
      ProofTree leq Γ' Δ'

  | weakening {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Γ' ->
      isFSet Δ' ->
      ProofTree leq Γ Δ ->
      sequentLeq leq Γ Δ Γ' Δ' ->
      ProofTree leq Γ' Δ'

  -- common rules
  | hypothesis {Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      ordContains leq α Ω₁ ->
      ordContains leq α Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | cut {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- left premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      -- right premise
      isFSet Δ₁ -> isFSet Δ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing
      Γ₁ ⊆ Ω₁ ->
      Δ₂ ⊆ Ω₂ ->
      -- only α removed
      ∀ φ ∈ (Γ₂ \ Ω₂), isSame leq α φ ->
      ∀ φ ∈ (Δ₁ \ Ω₁), isSame leq α φ ->
      ProofTree leq Ω₁ Ω₂

  -- left structural rules
  | leftAnd {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the right
      Γ₂ ⊆ Ω₂ ->
      -- only α and β removed on the left
      ∀ φ ∈ (Γ₁ \ Ω₁), isSame leq α φ ∨ isSame leq β φ ->
      -- α ∧ β added on the left
      ordContains leq (and α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂

  | leftOr {prems : List (AnnotatedSequent Expr)}
      {Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premises nonempty
      prems ≠ ∅ ->
      -- all premises well sorted
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, φ⟩ := prem
        isFSet Γ ∧ isFSet Δ ∧ isFormula φ
      ) ->
      isFormula α ->
      isFormula β ->
      -- all premises derivable
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, _⟩ := prem
        ProofTree leq Γ Δ
      ) ->
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, α⟩ := prem
        -- all rights preserved
        Δ ⊆ Ω₂ ∧
        -- all lefts preserved except α
        ∀ φ ∈ (Γ \ Ω₁), isSame leq α φ
      ) ->
      -- ⋁ᵢ αᵢ added on the left
      (
        let disjuncts :=
          prems.map (·.val)
        let disjunction :=
          match disjuncts with
          | [] => bot -- unreachable case
          | α :: βs => βs.foldl Expr.or α

        ordContains leq disjunction Ω₁
      ) ->
      ProofTree leq Ω₁ Ω₂

  | leftImp {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq Γ (insert φ Δ) ->
      ProofTree leq (insert ψ Ω) Ξ ->
      ProofTree leq (insert (imp φ ψ) (Γ ∪ Ω)) (Δ ∪ Ξ)

  | leftIff {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq (insert (imp φ ψ) (insert (imp ψ φ) Γ)) Δ ->
      ProofTree leq (insert (iff φ ψ) Γ) Δ

  | leftNot {Γ Δ : Finset Expr} (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      ProofTree leq Γ (insert φ Δ) ->
      ProofTree leq (insert (neg φ) Γ) Δ

  | leftForall {Γ Δ : Finset Expr} (x : SVar) (φ t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      isTerm t ->
      ProofTree leq (insert (substOne x t φ) Γ) Δ ->
      ProofTree leq (insert (forall_ x φ) Γ) Δ

  | leftExists {Γ Δ : Finset Expr} (x : SVar) (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      ProofTree leq (insert φ Γ) Δ ->
      x ∉ freeVars (insert (exists_ x φ) Γ ∪ Δ) ->
      ProofTree leq (insert (exists_ x φ) Γ) Δ

  -- right structural rules

  | rightAnd {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq Γ (insert φ Δ) ->
      ProofTree leq Ω (insert ψ Ξ) ->
      ProofTree leq (Γ ∪ Ω) (insert (and φ ψ) (Δ ∪ Ξ))

  | rightOr {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq Γ (insert φ (insert ψ Δ)) ->
      ProofTree leq Γ (insert (or φ ψ) Δ)

  | rightImp {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq (insert φ Γ) (insert ψ Δ) ->
      ProofTree leq Γ (insert (imp φ ψ) Δ)

  | rightIff {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq Γ (insert (imp φ ψ) Δ) ->
      ProofTree leq Ω (insert (imp ψ φ) Ξ) ->
      ProofTree leq (Γ ∪ Ω) (insert (iff φ ψ) (Δ ∪ Ξ))

  | rightNot {Γ Δ : Finset Expr} (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      ProofTree leq (insert φ Γ) Δ ->
      ProofTree leq Γ (insert (neg φ) Δ)

  | rightForall {Γ Δ : Finset Expr} (x : SVar) (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      ProofTree leq Γ (insert φ Δ) ->
      x ∉ freeVars (insert (forall_ x φ) Γ ∪ Δ) ->
      ProofTree leq Γ (insert (forall_ x φ) Δ)

  | rightExists {Γ Δ : Finset Expr} (x : SVar) (φ t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      isTerm t ->
      ProofTree leq Γ (insert (substOne x t φ) Δ) ->
      ProofTree leq Γ (insert (exists_ x φ) Δ)

  | rightEpsilon {Γ Δ : Finset Expr} (x : SVar) (φ t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      isTerm t ->
      ProofTree leq Γ (insert (substOne x t φ) Δ) ->
      ProofTree leq Γ (insert (substOne x (epsilon_ (.lam x φ)) φ) Δ)

  -- equality rules

  | leftRefl {Γ Δ : Finset Expr} (t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isTerm t ->
      ProofTree leq (insert (eq t t) Γ) Δ ->
      ProofTree leq Γ Δ

  | rightRefl (t : Expr) :
      isTerm t ->
      ProofTree leq ∅ {eq t t}

  | leftSubstEq {Γ Δ : Finset Expr} (x : SVar) (s t φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isTerm s ->
      isTerm t ->
      isFormula φ ->
      ProofTree leq (insert (substOne x s φ) Γ) Δ ->
      ProofTree leq (insert (eq s t) (insert (substOne x t φ) Γ)) Δ

  | rightSubstEq {Γ Δ : Finset Expr} (x : SVar) (s t φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isTerm s ->
      isTerm t ->
      isFormula φ ->
      ProofTree leq Γ (insert (substOne x s φ) Δ) ->
      ProofTree leq (insert (eq s t) Γ) (insert (substOne x t φ) Δ)

  | instSchema {Γ Δ : Finset Expr} (σ : Subst) :
      isFSet Γ ->
      isFSet Δ ->
      Subst.wellSorted σ ->
      ProofTree leq Γ Δ ->
      ProofTree leq (Γ.image (subst σ)) (Δ.image (subst σ))
