import Lisa.Order

open Lisa

structure SubstPair where
    source : Expr
    target : Expr

def SubstPair.wellSorted (σ : SubstPair) : Prop :=
  σ.source.wellSorted ∧ σ.source.sort = σ.target.sort

def SubstPair.sort (σ : SubstPair) : Option LSort :=
  σ.source.sort

/-- Quantify pointwise equality for functions and equivalence for predicates. -/
def SubstPair.liftEq (σ : SubstPair) : Expr :=
    match σ.sort with
    | none => -- malformed
        σ.source.eq σ.target
    | some sort =>
        -- if the sort is a function type,
        -- make a universally quantified equality
        let (args, result) := sort.splitArgs
        let allFree := σ.source.freeVars ∪ σ.target.freeVars
        let maxId := allFree.fold Nat.max 0 (·.id.idx)
        let vars := args.mapIdx fun i argSort =>
          let id := maxId + i + 1
          SVar.mk ⟨"x", id⟩ argSort
        let appliedSource := σ.source.applied (vars.map Expr.var)
        let appliedTarget := σ.target.applied (vars.map Expr.var)
        let baseEq := if result = prop then appliedSource.iff appliedTarget
          else appliedSource.eq appliedTarget

        vars.foldr Expr.forall_ baseEq

/-- Represent a substitution context by parameters and a formula body. -/
structure SubstContext where
  params : List SVar
  body : Expr

def SubstContext.wellSorted (φ : SubstContext) : Prop :=
  isFormula φ.body ∧ ∀ x ∈ φ.params, x.sort.isFunctional = true ∨ x.sort.isPredicate = true

/-- Instantiate simultaneously; repeated parameters use their last replacement. -/
def SubstContext.instantiate (φ : SubstContext) (args : List Expr) : Expr :=
  let σ := (φ.params.zip args).foldl (fun σ (x, e) => σ.insert x e) (∅ : Subst)
  σ.subst φ.body

/-- Check substitution arity and parameter sorts. -/
def SubstContext.fits (φ : SubstContext) (eqs : List SubstPair) : Prop :=
  eqs.map (·.sort) = φ.params.map (fun x => some x.sort)

namespace Ordered

open Expr

inductive ProofTree (leq : Order) : (Γ Δ : Finset Expr) -> Type where
  -- ordering rules
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
  | hypothesis (φ : Expr) :
      isFormula φ ->
      ProofTree leq {φ} {φ}

  | cut {Γ Ω Δ Ξ : Finset Expr} (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      ProofTree leq Γ (insert φ Δ) ->
      ProofTree leq (insert φ Ω) Ξ ->
      ProofTree leq (Γ ∪ Ω) (Δ ∪ Ξ)

  -- left structural rules
  | leftAnd {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq (insert φ (insert ψ Γ)) Δ ->
      ProofTree leq (insert (and φ ψ) Γ) Δ

  | leftOr {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree leq (insert φ Γ) Δ ->
      ProofTree leq (insert ψ Ω) Ξ ->
      ProofTree leq (insert (or φ ψ) (Γ ∪ Ω)) (Δ ∪ Ξ)

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

  | leftSubstEq {Γ Δ : Finset Expr} (eqs : List SubstPair) (φ : SubstContext) :
      isFSet Γ ->
      isFSet Δ ->
      (∀ σ ∈ eqs, σ.wellSorted) ->
      φ.wellSorted ->
      -- arguments of φ match the sorts of the subst pairs
      φ.fits eqs ->
      isFormula (φ.instantiate (eqs.map (·.source))) ->
      isFormula (φ.instantiate (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      -- Γ, φ(s_) ⊢ Δ
      ProofTree leq (insert (φ.instantiate (eqs.map (·.source))) Γ) Δ ->
      -- Γ, ∀x₁...xₙ. s₁(x_) = t₁(x_), ..., φ(t_) ⊢ Δ
      ProofTree leq
        (
            let liftedEqs := eqs.map (·.liftEq) |>.toFinset
            let φt := φ.instantiate (eqs.map (·.target))

            liftedEqs ∪ insert φt Γ
        )
        Δ

  | rightSubstEq {Γ Δ : Finset Expr} (eqs : List SubstPair) (φ : SubstContext) :
      isFSet Γ ->
      isFSet Δ ->
      (∀ σ ∈ eqs, σ.wellSorted) ->
      φ.wellSorted ->
      -- arguments of φ match the sorts of the subst pairs
      φ.fits eqs ->
      isFormula (φ.instantiate (eqs.map (·.source))) ->
      isFormula (φ.instantiate (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      -- Γ ⊢ φ(s_), Δ
      ProofTree leq Γ (insert (φ.instantiate (eqs.map (·.source))) Δ) ->
      -- ∀x₁...xₙ. s₁(x_) = t₁(x_), ..., Γ ⊢ φ(t_), Δ
      ProofTree leq
        (
            let liftedEqs := eqs.map (·.liftEq) |>.toFinset

            liftedEqs ∪ Γ
        )
        (insert (φ.instantiate (eqs.map (·.target))) Δ)

  | instSchema {Γ Δ : Finset Expr} (σ : Subst) :
      isFSet Γ ->
      isFSet Δ ->
      Subst.wellSorted σ ->
      ProofTree leq Γ Δ ->
      ProofTree leq (Γ.image (subst σ)) (Δ.image (subst σ))

end Ordered
