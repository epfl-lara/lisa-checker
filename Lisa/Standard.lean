import Lisa.Syntax

open Lisa

abbrev Order : Type := Expr -> Expr -> Prop

@[simp]
def isSame (leq : Order) (α β : Expr) : Prop :=
  leq α β ∧ leq β α

@[simp]
def ordContains (leq : Order) (α : Expr) (Γ : Finset Expr) : Prop :=
  ∃ β ∈ Γ, isSame leq α β

@[simp]
def setLeq (leq : Order) (s t : Finset Expr) : Prop :=
  ∀ φ ∈ s, ∃ ψ ∈ t, isSame leq φ ψ

def NegAntitone (leq : Order) : Prop :=
  ∀ {α β : Expr}, leq α β -> leq (.neg β) (.neg α)

def NegInvariant (leq : Order) : Prop :=
  ∀ {α β : Expr}, isSame leq α β -> isSame leq (.neg α) (.neg β)

@[simp]
lemma NegAntitone.negInvariant {leq : Order} (hneg : NegAntitone leq) :
    NegInvariant leq := by
  intro α β hsame
  exact ⟨hneg hsame.2, hneg hsame.1⟩

@[simp]
def sequentLeq (leq : Order) (Γ Δ Γ' Δ' : Finset Expr) : Prop :=
  let seq1 := (Γ.image Expr.neg) ∪ Δ
  let seq2 := (Γ'.image Expr.neg) ∪ Δ'
  setLeq leq seq1 seq2

structure SubstPair where
    source : Expr
    target : Expr

def SubstPair.wellSorted (σ : SubstPair) : Prop :=
  σ.source.wellSorted ∧ σ.source.sort = σ.target.sort

def SubstPair.sort (σ : SubstPair) : Option LSort :=
  σ.source.sort

def SubstPair.liftEq (σ : SubstPair) : Expr :=
    match σ.sort with
    | none => -- malformed
        σ.source.eq σ.target
    | some sort =>
        -- if the sort is a function type,
        -- make a universally quantified equality
        let (args, _) := sort.splitArgs
        let allFree := σ.source.freeVars ∪ σ.target.freeVars
        let maxId := allFree.fold Nat.max 0 (·.id.idx)
        let vars := args.mapIdx fun i argSort =>
          let id := maxId + i + 1
          SVar.mk ⟨"x", id⟩ argSort
        let appliedSource := σ.source.applied (vars.map Expr.var)
        let appliedTarget := σ.target.applied (vars.map Expr.var)
        let baseEq := appliedSource.eq appliedTarget

        vars.foldr Expr.forall_ baseEq

namespace Standard

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

  | leftSubstEq {Γ Δ : Finset Expr} (eqs : List SubstPair) (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
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
      -- Γ, φ(s_) ⊢ Δ
      ProofTree leq (insert (φ.applied (eqs.map (·.source))) Γ) Δ ->
      -- Γ, ∀x₁...xₙ. s₁(x_) = t₁(x_), ..., φ(t_) ⊢ Δ
      ProofTree leq
        (
            let liftedEqs := eqs.map (·.liftEq) |>.toFinset
            let φt := φ.applied (eqs.map (·.target))

            liftedEqs ∪ insert φt Γ
        )
        Δ

  | rightSubstEq {Γ Δ : Finset Expr} (eqs : List SubstPair) (φ : Expr) :
      isFSet Γ ->
      isFSet Δ ->
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
      -- Γ ⊢ φ(s_), Δ
      ProofTree leq Γ (insert (φ.applied (eqs.map (·.source))) Δ) ->
      -- ∀x₁...xₙ. s₁(x_) = t₁(x_), ..., Γ ⊢ φ(t_), Δ
      ProofTree leq
        (
            let liftedEqs := eqs.map (·.liftEq) |>.toFinset

            liftedEqs ∪ Γ
        )
        (insert (φ.applied (eqs.map (·.target))) Δ)

  | instSchema {Γ Δ : Finset Expr} (σ : Subst) :
      isFSet Γ ->
      isFSet Δ ->
      Subst.wellSorted σ ->
      ProofTree leq Γ Δ ->
      ProofTree leq (Γ.image (subst σ)) (Δ.image (subst σ))

end Standard
