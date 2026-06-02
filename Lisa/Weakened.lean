import Lisa.Syntax
import Lisa.Ordered

/-
  This module defined the order-weakened λFOL proof system as used by the Lisa
  proof checker.
-/

open Lisa

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
      ProofTree leq Γ₁ Γ₂ ->
      -- right premise
      isFSet Δ₁ -> isFSet Δ₂ ->
      ProofTree leq Δ₁ Δ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing
      Γ₁ ⊆ Ω₁ ->
      Δ₂ ⊆ Ω₂ ->
      -- only α removed
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq α φ) ->
      (∀ φ ∈ (Δ₁ \ Ω₁), isSame leq α φ) ->
      ProofTree leq Ω₁ Ω₂

  -- left structural rules
  | leftAnd {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the right
      Γ₂ ⊆ Ω₂ ->
      -- only α and β removed on the left
      (∀ φ ∈ (Γ₁ \ Ω₁), isSame leq α φ ∨ isSame leq β φ) ->
      -- α ∧ β added on the left
      ordContains leq (and α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂

  | leftOr {prems : List (AnnotatedSequent Expr)}
      {Ω₁ Ω₂ : Finset Expr} :
      -- premises nonempty
      prems ≠ ∅ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- all premises well sorted
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, φ⟩ := prem
        isFSet Γ ∧ isFSet Δ ∧ isFormula φ
      ) ->
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
        let disjuncts := prems.map (·.val)
        let disjunction :=
          match disjuncts with
          | [] => bot -- unreachable case
          | α :: βs => βs.foldl Expr.or α

        ordContains leq disjunction Ω₁
      ) ->
      ProofTree leq Ω₁ Ω₂

  | leftImp {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- left premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- right premise
      isFSet Δ₁ -> isFSet Δ₂ ->
      ProofTree leq Δ₁ Δ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing unnecessary removed
      Γ₁ ⊆ Ω₁ ->
      Δ₂ ⊆ Ω₂ ->
      -- only α removed from the first premise right
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq α φ) ->
      -- only β removed from the second premise left
      (∀ ψ ∈ (Δ₁ \ Ω₁), isSame leq β ψ) ->
      -- α => β added on the left
      ordContains leq (imp α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂

  | leftIff {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the right
      Γ₂ ⊆ Ω₂ ->
      -- only implications removed on the left
      (∀ φ ∈ (Γ₁ \ Ω₁), isSame leq (imp α β) φ ∨ isSame leq (imp β α) φ) ->
      -- α <=> β added on the left
      ordContains leq (iff α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂

  | leftNot {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing on the left
      Γ₁ ⊆ Ω₁ ->
      -- only α removed on the right
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq α φ) ->
      -- ¬α added on the left
      ordContains leq (neg α) Ω₁ ->
      ProofTree leq Ω₁ Ω₂

  | leftForall {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      isTerm t ->
      -- nothing missing on the right
      Γ₂ ⊆ Ω₂ ->
      -- only α[t/x] removed on the left
      (∀ φ ∈ (Γ₁ \ Ω₁), isSame leq (substOne x t α) φ) ->
      -- ∀x. α added on the left
      ordContains leq (forall_ x α) Ω₁ ->
      ProofTree leq Ω₁ Ω₂

  | leftExists {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      -- nothing missing on the right
      Γ₂ ⊆ Ω₂ ->
      -- only α removed on the left
      (∀ φ ∈ (Γ₁ \ Ω₁), isSame leq α φ) ->
      -- ∃x. α added on the left
      ordContains leq (exists_ x α) Ω₁ ->
      -- x not free in conclusion
      x ∉ freeVars (Ω₁ ∪ Ω₂) ->
      ProofTree leq Ω₁ Ω₂

  -- right structural rules

  | rightAnd {prems : List (AnnotatedSequent Expr)}
      {Ω₁ Ω₂ : Finset Expr} :
      -- premises nonempty
      prems ≠ ∅ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- all premises well sorted
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, φ⟩ := prem
        isFSet Γ ∧ isFSet Δ ∧ isFormula φ
      ) ->
      -- all premises derivable
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, _⟩ := prem
        ProofTree leq Γ Δ
      ) ->
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, α⟩ := prem
        -- all lefts preserved
        Γ ⊆ Ω₁ ∧
        -- all rights preserved except α
        ∀ φ ∈ (Δ \ Ω₂), isSame leq α φ
      ) ->
      -- ⋀ᵢ αᵢ added on the right
      (
        let conjuncts := prems.map (·.val)
        let conjunction :=
          match conjuncts with
          | [] => top -- unreachable case
          | α :: βs => βs.foldl Expr.and α

        ordContains leq conjunction Ω₂
      ) ->
      ProofTree leq Ω₁ Ω₂

  | rightOr {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the left
      Γ₁ ⊆ Ω₁ ->
      -- only α and β removed on the right
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq α φ ∨ isSame leq β φ) ->
      -- α ∨ β added on the right
      ordContains leq (or α β) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | rightImp {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- only α removed on the left
      (∀ φ ∈ (Γ₁ \ Ω₁), isSame leq α φ) ->
      -- only β removed on the right
      (∀ ψ ∈ (Γ₂ \ Ω₂), isSame leq β ψ) ->
      -- α => β added on the right
      ordContains leq (imp α β) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | rightIff {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- left premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- right premise
      isFSet Δ₁ -> isFSet Δ₂ ->
      ProofTree leq Δ₁ Δ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the left
      Γ₁ ⊆ Ω₁ ->
      Δ₁ ⊆ Ω₁ ->
      -- only implications removed on the right
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq (imp α β) φ) ->
      (∀ φ ∈ (Δ₂ \ Ω₂), isSame leq (imp β α) φ) ->
      -- α <=> β added on the right
      ordContains leq (iff α β) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | rightNot {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing on the right
      Γ₂ ⊆ Ω₂ ->
      -- only α removed on the left
      (∀ φ ∈ (Γ₁ \ Ω₁), isSame leq α φ) ->
      -- ¬α added on the right
      ordContains leq (neg α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | rightForall {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      -- nothing missing on the left
      Γ₁ ⊆ Ω₁ ->
      -- only α removed on the right
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq α φ) ->
      -- ∀x. α added on the right
      ordContains leq (forall_ x α) Ω₂ ->
      -- x not free in conclusion
      x ∉ freeVars (Ω₁ ∪ Ω₂) ->
      ProofTree leq Ω₁ Ω₂

  | rightExists {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      isTerm t ->
      -- nothing missing on the left
      Γ₁ ⊆ Ω₁ ->
      -- only α[t/x] removed on the right
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq (substOne x t α) φ) ->
      -- ∃x. α added on the right
      ordContains leq (exists_ x α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | rightEpsilon {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      isTerm t ->
      -- nothing missing on the left
      Γ₁ ⊆ Ω₁ ->
      -- only α[t/x] removed on the right
      (∀ φ ∈ (Γ₂ \ Ω₂), isSame leq (substOne x t α) φ) ->
      -- ε instantiation added on the right
      ordContains leq (substOne x (epsilon_ (.lam x α)) α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  -- equality rules

  | leftRefl {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- reflexive term
      isTerm t ->
      -- right preserved
      Γ₂ ⊆ Ω₂ ->
      -- only eq t t removed on the left
      (∀ φ ∈ (Γ₁ \ Ω₁), isSame leq (eq t t) φ) ->
      ProofTree leq Ω₁ Ω₂

  | rightRefl {Ω₁ Ω₂ : Finset Expr} (t : Expr) :
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- reflexive term
      isTerm t ->
      -- eq t t added on the right
      ordContains leq (eq t t) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | leftSubstEq {Γ₁ Γ₂ Ω₁ Ω₂: Finset Expr} (eqs : List SubstPair) (φ : Expr) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      isFSet Ω₁ -> isFSet Ω₂ ->
      (∀ σ ∈ eqs, σ.wellSorted) ->
      φ.wellSorted ->
      -- arguments of φ match the sorts of the subst pairs
      (
        match φ.sort with
        | none => False
        | some sort =>
            let (args, _) := sort.splitArgs
            eqs.map (·.sort) = args.map some
      ) ->
      isFormula (φ.applied (eqs.map (·.source))) ->
      isFormula (φ.applied (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      -- left preserved except φ(s_)
      (
        let φs := φ.applied (eqs.map (·.source))

        setLeq leq Γ₁ (Ω₁ ∪ {φs})
      ) ->
      -- equalities and φ(t_) added
      (
        let liftedEqs := eqs.map (·.liftEq) |>.toFinset
        let φt := φ.applied (eqs.map (·.target))

        setLeq leq (liftedEqs ∪ {φt}) Ω₁
      ) ->
      -- right preserved
      Γ₂ ⊆ Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | rightSubstEq {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (eqs : List SubstPair) (φ : Expr) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      isFSet Ω₁ -> isFSet Ω₂ ->
      (∀ σ ∈ eqs, σ.wellSorted) ->
      φ.wellSorted ->
      -- arguments of φ match the sorts of the subst pairs
      (
        match φ.sort with
        | none => False
        | some sort =>
            let (args, _) := sort.splitArgs
            eqs.map (·.sort) = args.map some
      ) ->
      isFormula (φ.applied (eqs.map (·.source))) ->
      isFormula (φ.applied (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      -- left preserved + equalities added
      (
        let liftedEqs := eqs.map (·.liftEq) |>.toFinset

        setLeq leq (Γ₁ ∪ liftedEqs) Ω₁
      ) ->
      -- right preserved except φ(s_) swapped with φ(t_)
      (
        let φs := φ.applied (eqs.map (·.source))
        let φt := φ.applied (eqs.map (·.target))

        setLeq leq Γ₂ (Ω₂ ∪ {φs}) ∧ ordContains leq φt Ω₂
      ) ->
      ProofTree leq Ω₁ Ω₂

  | instSchema {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (σ : Subst) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      isFSet Ω₁ -> isFSet Ω₂ ->
      Subst.wellSorted σ ->
      -- the substituted sequent can be weakened
      -- to the conclusion
      (
        let Γ₁' := Γ₁.image (Subst.subst σ)
        let Γ₂' := Γ₂.image (Subst.subst σ)

        sequentLeq leq Γ₁' Γ₂' Ω₁ Ω₂
      ) ->
      ProofTree leq Ω₁ Ω₂
