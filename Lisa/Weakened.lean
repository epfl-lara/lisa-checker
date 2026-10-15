import Lisa.Syntax
import Lisa.Ordered

/-
  Define Lisa's order-weakened λFOL rules, parameterized by a formula order
  and an equivalence-preserving order reduction.
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

inductive ProofTree (leq : Order) [OrderReduction leq] : (Γ Δ : Finset Expr) -> Type where
  -- ordering rules
  -- Compare the whole-sequent formulas.
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

  /-- Introduce a sequent whose whole formula is order-equivalent to truth. -/
  | restateTrue {Ω₁ Ω₂ : Finset Expr} :
      isFSet Ω₁ → isFSet Ω₂ →
      isSame leq (sequentToFormula Ω₁ Ω₂) top →
      ProofTree leq Ω₁ Ω₂

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
      reducedSubset leq Γ₁ Ω₁ ->
      reducedSubset leq Δ₂ Ω₂ ->
      -- only α removed
      containedExcept leq Γ₂ Ω₂ (α) ->
      containedExcept leq Δ₁ Ω₁ (α) ->
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
      reducedSubset leq Γ₂ Ω₂ ->
      -- only α and β removed on the left
      containedExceptEither leq Γ₁ Ω₁ (α) (β) ->
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
        reducedSubset leq Δ Ω₂ ∧
        -- all lefts preserved except α
        containedExcept leq Γ Ω₁ (α)
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
      reducedSubset leq Γ₁ Ω₁ ->
      reducedSubset leq Δ₂ Ω₂ ->
      -- only α removed from the first premise right
      containedExcept leq Γ₂ Ω₂ (α) ->
      -- only β removed from the second premise left
      containedExcept leq Δ₁ Ω₁ (β) ->
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
      reducedSubset leq Γ₂ Ω₂ ->
      -- only implications removed on the left
      containedExceptEither leq Γ₁ Ω₁ ((imp α β)) ((imp β α)) ->
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
      reducedSubset leq Γ₁ Ω₁ ->
      -- only α removed on the right
      containedExcept leq Γ₂ Ω₂ (α) ->
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
      reducedSubset leq Γ₂ Ω₂ ->
      -- only α[t/x] removed on the left
      containedExcept leq Γ₁ Ω₁ ((substOne x t α)) ->
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
      reducedSubset leq Γ₂ Ω₂ ->
      -- only α removed on the left
      containedExcept leq Γ₁ Ω₁ (α) ->
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
        reducedSubset leq Γ Ω₁ ∧
        -- all rights preserved except α
        containedExcept leq Δ Ω₂ (α)
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
      reducedSubset leq Γ₁ Ω₁ ->
      -- only α and β removed on the right
      containedExceptEither leq Γ₂ Ω₂ (α) (β) ->
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
      containedExcept leq Γ₁ Ω₁ (α) ->
      -- only β removed on the right
      containedExcept leq Γ₂ Ω₂ (β) ->
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
      reducedSubset leq Γ₁ Ω₁ ->
      reducedSubset leq Δ₁ Ω₁ ->
      -- only implications removed on the right
      containedExcept leq Γ₂ Ω₂ ((imp α β)) ->
      containedExcept leq Δ₂ Ω₂ ((imp β α)) ->
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
      reducedSubset leq Γ₂ Ω₂ ->
      -- only α removed on the left
      containedExcept leq Γ₁ Ω₁ (α) ->
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
      reducedSubset leq Γ₁ Ω₁ ->
      -- only α removed on the right
      containedExcept leq Γ₂ Ω₂ (α) ->
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
      reducedSubset leq Γ₁ Ω₁ ->
      -- only α[t/x] removed on the right
      containedExcept leq Γ₂ Ω₂ ((substOne x t α)) ->
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
      reducedSubset leq Γ₁ Ω₁ ->
      -- only α[t/x] removed on the right
      containedExcept leq Γ₂ Ω₂ ((substOne x t α)) ->
      -- ε instantiation added on the right
      ordContains leq (substOne x (epsilon_ (.lam x α)) α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  -- equality rules

  | leftRefl {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (s t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- reflexive term
      isTerm s -> isTerm t ->
      isSame leq s t ->
      -- right preserved
      reducedSubset leq Γ₂ Ω₂ ->
      -- only the reflexive equality removed on the left
      containedExcept leq Γ₁ Ω₁ ((eq s t)) ->
      ProofTree leq Ω₁ Ω₂

  | rightRefl {Ω₁ Ω₂ : Finset Expr} (s t : Expr) :
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- reflexive term
      isTerm s -> isTerm t ->
      isSame leq s t ->
      -- the reflexive equality added on the right
      ordContains leq (eq s t) Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | leftSubstEq {Γ₁ Γ₂ Ω₁ Ω₂: Finset Expr} (eqs : List SubstPair) (φ : SubstContext) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      isFSet Ω₁ -> isFSet Ω₂ ->
      (∀ σ ∈ eqs, σ.wellSorted) ->
      φ.wellSorted ->
      -- arguments of φ match the sorts of the subst pairs
      φ.fits eqs ->
      isFormula (φ.instantiate (eqs.map (·.source))) ->
      isFormula (φ.instantiate (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      -- left preserved except φ(s_)
      (
        let φs := φ.instantiate (eqs.map (·.source))

        containedExcept leq Γ₁ Ω₁ φs
      ) ->
      -- equalities and φ(t_) added
      (
        let liftedEqs := eqs.map (·.liftEq) |>.toFinset
        let φt := φ.instantiate (eqs.map (·.target))

        setLeq leq (liftedEqs ∪ {φt}) Ω₁
      ) ->
      -- right preserved
      reducedSubset leq Γ₂ Ω₂ ->
      ProofTree leq Ω₁ Ω₂

  | rightSubstEq {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (eqs : List SubstPair) (φ : SubstContext) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      isFSet Ω₁ -> isFSet Ω₂ ->
      (∀ σ ∈ eqs, σ.wellSorted) ->
      φ.wellSorted ->
      -- arguments of φ match the sorts of the subst pairs
      φ.fits eqs ->
      isFormula (φ.instantiate (eqs.map (·.source))) ->
      isFormula (φ.instantiate (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      -- left preserved + equalities added
      (
        let liftedEqs := eqs.map (·.liftEq) |>.toFinset

        reducedSubset leq Γ₁ Ω₁ ∧ setLeq leq liftedEqs Ω₁
      ) ->
      -- right preserved except φ(s_) swapped with φ(t_)
      (
        let φs := φ.instantiate (eqs.map (·.source))
        let φt := φ.instantiate (eqs.map (·.target))

        containedExcept leq Γ₂ Ω₂ φs ∧ ordContains leq φt Ω₂
      ) ->
      ProofTree leq Ω₁ Ω₂

  | instSchema {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (σ : Subst) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ->
      isFSet Ω₁ -> isFSet Ω₂ ->
      Subst.wellSorted σ ->
      -- Preserve each instantiated formula on its original side.
      (
        let Γ₁' := Γ₁.image (Subst.subst σ)
        let Γ₂' := Γ₂.image (Subst.subst σ)

        setLeq leq Γ₁' Ω₁ ∧ setLeq leq Γ₂' Ω₂
      ) ->
      ProofTree leq Ω₁ Ω₂
