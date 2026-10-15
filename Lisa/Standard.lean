import Lisa.Ordered

open Lisa

namespace Standard

open Expr

inductive ProofTree : (Γ Δ : Finset Expr) -> Type where
  -- structural rules
  | weakening {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Γ' ->
      isFSet Δ' ->
      ProofTree Γ Δ ->
      Γ ⊆ Γ' ->
      Δ ⊆ Δ' ->
      ProofTree Γ' Δ'

  -- common rules
  | hypothesis (φ : Expr) :
      isFormula φ ->
      ProofTree {φ} {φ}

  | cut {Γ Ω Δ Ξ : Finset Expr} (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      ProofTree Γ (insert φ Δ) ->
      ProofTree (insert φ Ω) Ξ ->
      ProofTree (Γ ∪ Ω) (Δ ∪ Ξ)

  -- left structural rules
  | leftAnd {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree (insert φ (insert ψ Γ)) Δ ->
      ProofTree (insert (and φ ψ) Γ) Δ

  | leftOr {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree (insert φ Γ) Δ ->
      ProofTree (insert ψ Ω) Ξ ->
      ProofTree (insert (or φ ψ) (Γ ∪ Ω)) (Δ ∪ Ξ)

  | leftImp {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree Γ (insert φ Δ) ->
      ProofTree (insert ψ Ω) Ξ ->
      ProofTree (insert (imp φ ψ) (Γ ∪ Ω)) (Δ ∪ Ξ)

  | leftIff {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree (insert (imp φ ψ) (insert (imp ψ φ) Γ)) Δ ->
      ProofTree (insert (iff φ ψ) Γ) Δ

  | leftNot {Γ Δ : Finset Expr} (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      ProofTree Γ (insert φ Δ) ->
      ProofTree (insert (neg φ) Γ) Δ

  | leftForall {Γ Δ : Finset Expr} (x : SVar) (φ t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      isTerm t ->
      ProofTree (insert (substOne x t φ) Γ) Δ ->
      ProofTree (insert (forall_ x φ) Γ) Δ

  | leftExists {Γ Δ : Finset Expr} (x : SVar) (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      ProofTree (insert φ Γ) Δ ->
      x ∉ freeVars (insert (exists_ x φ) Γ ∪ Δ) ->
      ProofTree (insert (exists_ x φ) Γ) Δ

  -- right structural rules

  | rightAnd {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree Γ (insert φ Δ) ->
      ProofTree Ω (insert ψ Ξ) ->
      ProofTree (Γ ∪ Ω) (insert (and φ ψ) (Δ ∪ Ξ))

  | rightOr {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree Γ (insert φ (insert ψ Δ)) ->
      ProofTree Γ (insert (or φ ψ) Δ)

  | rightImp {Γ Δ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree (insert φ Γ) (insert ψ Δ) ->
      ProofTree Γ (insert (imp φ ψ) Δ)

  | rightIff {Γ Ω Δ Ξ : Finset Expr} (φ ψ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Ω ->
      isFSet Ξ ->
      isFormula φ ->
      isFormula ψ ->
      ProofTree Γ (insert (imp φ ψ) Δ) ->
      ProofTree Ω (insert (imp ψ φ) Ξ) ->
      ProofTree (Γ ∪ Ω) (insert (iff φ ψ) (Δ ∪ Ξ))

  | rightNot {Γ Δ : Finset Expr} (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isFormula φ ->
      ProofTree (insert φ Γ) Δ ->
      ProofTree Γ (insert (neg φ) Δ)

  | rightForall {Γ Δ : Finset Expr} (x : SVar) (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      ProofTree Γ (insert φ Δ) ->
      x ∉ freeVars (insert (forall_ x φ) Γ ∪ Δ) ->
      ProofTree Γ (insert (forall_ x φ) Δ)

  | rightExists {Γ Δ : Finset Expr} (x : SVar) (φ t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      isTerm t ->
      ProofTree Γ (insert (substOne x t φ) Δ) ->
      ProofTree Γ (insert (exists_ x φ) Δ)

  | rightEpsilon {Γ Δ : Finset Expr} (x : SVar) (φ t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      x.sort = ind ->
      isFormula φ ->
      isTerm t ->
      ProofTree Γ (insert (substOne x t φ) Δ) ->
      ProofTree Γ (insert (substOne x (epsilon_ (.lam x φ)) φ) Δ)

  -- equality rules

  | leftRefl {Γ Δ : Finset Expr} (t : Expr) :
      isFSet Γ ->
      isFSet Δ ->
      isTerm t ->
      ProofTree (insert (eq t t) Γ) Δ ->
      ProofTree Γ Δ

  | rightRefl (t : Expr) :
      isTerm t ->
      ProofTree ∅ {eq t t}

  | leftSubstEq {Γ Δ : Finset Expr} (eqs : List SubstPair) (φ : SubstContext) :
      isFSet Γ ->
      isFSet Δ ->
      (∀ σ ∈ eqs, σ.wellSorted) ->
      φ.wellSorted ->
      φ.fits eqs ->
      isFormula (φ.instantiate (eqs.map (·.source))) ->
      isFormula (φ.instantiate (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      ProofTree (insert (φ.instantiate (eqs.map (·.source))) Γ) Δ ->
      ProofTree
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
      φ.fits eqs ->
      isFormula (φ.instantiate (eqs.map (·.source))) ->
      isFormula (φ.instantiate (eqs.map (·.target))) ->
      isFSet (eqs.map (·.liftEq) |>.toFinset) ->
      ProofTree Γ (insert (φ.instantiate (eqs.map (·.source))) Δ) ->
      ProofTree
        (
            let liftedEqs := eqs.map (·.liftEq) |>.toFinset

            liftedEqs ∪ Γ
        )
        (insert (φ.instantiate (eqs.map (·.target))) Δ)

  | instSchema {Γ Δ : Finset Expr} (σ : Subst) :
      isFSet Γ ->
      isFSet Δ ->
      Subst.wellSorted σ ->
      ProofTree Γ Δ ->
      ProofTree (Γ.image (subst σ)) (Δ.image (subst σ))

end Standard
