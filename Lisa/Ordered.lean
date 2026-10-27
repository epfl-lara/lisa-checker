import Lisa.Order
import Lisa.Sorting

open Lisa

structure SubstPair where
    source : Expr
    target : Expr

def SubstPair.wellSorted (σ : SubstPair) : Prop :=
  σ.source.wellSorted ∧ σ.source.sort = σ.target.sort

def SubstPair.sort (σ : SubstPair) : Option LSort :=
  σ.source.sort

/-- Compare fully applied results by individual equality or propositional equivalence. -/
def SubstPair.pointwiseEq (σ : SubstPair) (xs : List SVar) : Expr :=
  let source := σ.source.applied (xs.map Expr.var)
  let target := σ.target.applied (xs.map Expr.var)
  if σ.sort.map (fun s => s.splitArgs.2) = some prop then source.iff target
  else source.eq target

/-- Independent arguments of the required sorts, fresh for both compared expressions.
Freshness for the comparison premise's other formulas is checked by the proof rule.
-/
def SubstPair.validParams (σ : SubstPair) (xs : List SVar) : Prop :=
  σ.wellSorted ∧
  (match σ.sort with
    | none => False
    | some s => xs.map SVar.sort = s.splitArgs.1) ∧
  xs.Nodup ∧ ∀ x ∈ xs, x ∉ σ.source.freeVars ∪ σ.target.freeVars

instance (σ : SubstPair) (xs : List SVar) : Decidable (σ.validParams xs) := by
  unfold SubstPair.validParams SubstPair.wellSorted Expr.wellSorted
  cases σ.sort <;> infer_instance

theorem SubstPair.applied_splitArgs_sort (s : LSort) {e : Expr} (he : e.hasSort s)
    (xs : List SVar) (hxs : xs.map SVar.sort = s.splitArgs.1) :
    (e.applied (xs.map Expr.var)).hasSort s.splitArgs.2 := by
  induction s generalizing e xs with
  | ind =>
      have : xs = [] := by simpa [LSort.splitArgs] using hxs
      subst xs
      exact he
  | prop =>
      have : xs = [] := by simpa [LSort.splitArgs] using hxs
      subst xs
      exact he
  | arrow a b _ ih =>
      cases xs with
      | nil => simp [LSort.splitArgs] at hxs
      | cons x xs =>
          simp only [List.map_cons, LSort.splitArgs, List.cons.injEq] at hxs
          apply ih (e := .app e (.var x)) (xs := xs) _ hxs.2
          change e.sort = some (a >> b) at he
          simp [Expr.hasSort, Expr.sort, he, hxs.1]

theorem SubstPair.splitArgs_ground (s : LSort) :
    s.splitArgs.2 = ind ∨ s.splitArgs.2 = prop := by
  induction s with
  | ind => exact Or.inl rfl
  | prop => exact Or.inr rfl
  | arrow _ _ _ ih => exact ih

/-- Valid comparison parameters always produce a formula. -/
theorem SubstPair.pointwiseEq_isFormula {σ : SubstPair} {xs : List SVar}
    (h : σ.validParams xs) : isFormula (σ.pointwiseEq xs) := by
  obtain ⟨⟨hs, hst⟩, hxs, _, _⟩ := h
  cases he : σ.source.sort with
  | none => simp [Expr.wellSorted, he] at hs
  | some s =>
      have hargs : xs.map SVar.sort = s.splitArgs.1 := by
        simpa [SubstPair.sort, he] using hxs
      have hsource := SubstPair.applied_splitArgs_sort s he xs hargs
      have htarget := SubstPair.applied_splitArgs_sort s (hst.symm.trans he) xs hargs
      rcases SubstPair.splitArgs_ground s with hb | hb
      · rw [hb] at hsource htarget
        simpa [SubstPair.pointwiseEq, SubstPair.sort, he, hb] using
          isFormula_eq hsource htarget
      · rw [hb] at hsource htarget
        simpa [SubstPair.pointwiseEq, SubstPair.sort, he, hb] using
          isFormula_iff hsource htarget

/-- Represent a substitution context by parameters and a formula body. -/
structure SubstContext where
  params : List SVar
  body : Expr

/-- Instantiate simultaneously; repeated parameters use their last replacement. -/
def SubstContext.instantiate (φ : SubstContext) (args : List Expr) : Expr :=
  let σ := (φ.params.zip args).foldl (fun σ (x, e) => σ.insert x e) (∅ : Subst)
  σ.subst φ.body

/-- Check substitution arity and parameter sorts. -/
def SubstContext.fits (φ : SubstContext) (eqs : List SubstPair) : Prop :=
  eqs.map (·.sort) = φ.params.map (fun x => some x.sort)

/-- Simultaneous replacements, each with its independent comparison arguments. -/
structure SubstRule where
  comparisons : List (SubstPair × List SVar)
  context : SubstContext

namespace SubstRule

def source (r : SubstRule) : Expr :=
  r.context.instantiate (r.comparisons.map (fun c => c.1.source))

def target (r : SubstRule) : Expr :=
  r.context.instantiate (r.comparisons.map (fun c => c.1.target))

/-- The second premise proves all pointwise comparisons together. -/
def equation (r : SubstRule) : Expr :=
  foldFormulas Expr.and Expr.top (r.comparisons.map (fun c => c.1.pointwiseEq c.2))

/-- Check the formula context and replacements; parameters may have any simple sort. -/
def valid (r : SubstRule) : Prop :=
  isFormula r.context.body ∧ r.context.fits (r.comparisons.map Prod.fst) ∧
  (∀ c ∈ r.comparisons, c.1.validParams c.2) ∧
  isFormula r.source ∧ isFormula r.target

/-- Only the comparison premise's residual contexts must be independent of its parameters. -/
def fresh (r : SubstRule) (Θ Ξ : Finset Expr) : Prop :=
  ∀ c ∈ r.comparisons, ∀ x ∈ c.2, x ∉ freeVars (Θ ∪ Ξ)

instance (r : SubstRule) : Decidable r.valid := by
  unfold valid SubstContext.fits isFormula Expr.hasSort
  infer_instance

instance (r : SubstRule) (Θ Ξ : Finset Expr) : Decidable (r.fresh Θ Ξ) := by
  unfold fresh
  infer_instance

theorem equation_isFormula {r : SubstRule} (h : r.valid) : isFormula r.equation := by
  have fold : ∀ (es : List Expr) (e : Expr), isFormula e →
      (∀ f ∈ es, isFormula f) → isFormula (es.foldl Expr.and e) := by
    intro es
    induction es with
    | nil => intro e he _; exact he
    | cons f fs ih =>
        intro e he hs
        exact ih (Expr.and e f) (isFormula_and he (hs f (by simp)))
          (fun g hg => hs g (by simp [hg]))
  have hs : ∀ e ∈ r.comparisons.map (fun c => c.1.pointwiseEq c.2), isFormula e := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    exact SubstPair.pointwiseEq_isFormula (h.2.2.1 c hc)
  unfold equation foldFormulas
  generalize r.comparisons.map (fun c => c.1.pointwiseEq c.2) = es at hs ⊢
  cases es with
  | nil => rfl
  | cons e es =>
      exact fold es e (hs e (by simp)) (fun f hf => hs f (by simp [hf]))

end SubstRule

namespace Ordered

open Expr

inductive ProofTree (leq : ExprRel) : (Γ Δ : Finset Expr) -> Type where
  -- ordering rules
  | restateWeaken {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Γ' ->
      isFSet Δ' ->
      ProofTree leq Γ Δ ->
      sequentLeq leq Γ Δ Γ' Δ' ->
      ProofTree leq Γ' Δ'

  -- common rules
  /-- Ordinary structural weakening, independent of the comparison relation. -/
  | weakening {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Γ' ->
      isFSet Δ' ->
      ProofTree leq Γ Δ ->
      Γ ⊆ Γ' ->
      Δ ⊆ Δ' ->
      ProofTree leq Γ' Δ'

  /-- Truth is provable without assumptions. -/
  | rightTrue : ProofTree leq ∅ {top}

  /-- Falsehood entails the empty succedent. -/
  | leftFalse : ProofTree leq {bot} ∅

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

  /-- Replace simultaneously on the left using an independently proved comparison. -/
  | leftSubst {Γ Δ Θ Ξ : Finset Expr} (r : SubstRule) :
      isFSet Γ -> isFSet Δ -> isFSet Θ -> isFSet Ξ ->
      r.valid -> r.fresh Θ Ξ ->
      ProofTree leq (insert r.source Γ) Δ ->
      ProofTree leq Θ (insert r.equation Ξ) ->
      ProofTree leq (insert r.target (Γ ∪ Θ)) (Δ ∪ Ξ)

  /-- Replace simultaneously on the right using an independently proved comparison. -/
  | rightSubst {Γ Δ Θ Ξ : Finset Expr} (r : SubstRule) :
      isFSet Γ -> isFSet Δ -> isFSet Θ -> isFSet Ξ ->
      r.valid -> r.fresh Θ Ξ ->
      ProofTree leq Γ (insert r.source Δ) ->
      ProofTree leq Θ (insert r.equation Ξ) ->
      ProofTree leq (Γ ∪ Θ) (insert r.target (Δ ∪ Ξ))

  | instSchema {Γ Δ : Finset Expr} (σ : Subst) :
      isFSet Γ ->
      isFSet Δ ->
      Subst.wellSorted σ ->
      ProofTree leq Γ Δ ->
      ProofTree leq (Γ.image (subst σ)) (Δ.image (subst σ))

end Ordered
