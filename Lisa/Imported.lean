import Lisa.Weakened

open Lisa Expr

namespace Imported

abbrev Sequent := Finset Expr × Finset Expr
abbrev Premise := AnnotatedSequent (Expr × Finset Sequent)

/-- Collect the assumptions of all premises, including repeated premises. -/
def premiseAssumptions (prems : List Premise) : Finset Sequent :=
  prems.foldr (fun p acc => p.val.2 ∪ acc) ∅

@[simp] theorem mem_premiseAssumptions (s : Sequent) (prems : List Premise) :
    s ∈ premiseAssumptions prems ↔ ∃ p ∈ prems, s ∈ p.val.2 := by
  induction prems with
  | nil => simp [premiseAssumptions]
  | cons p ps ih =>
    change s ∈ p.val.2 ∪ premiseAssumptions ps ↔ _
    simp only [Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]

/-- Compare whole-sequent formulas, as in kernel discharge. -/
noncomputable def sameSequent (leq : ExprRel) (s t : Sequent) : Prop :=
  sequentLeq leq s.1 s.2 t.1 t.2 ∧ sequentLeq leq t.1 t.2 s.1 s.2

/-- Remove every assumption equivalent to the justification's conclusion. -/
noncomputable def discharged (leq : ExprRel) (ss : Finset Sequent) (s : Sequent) :
    Finset Sequent :=
  by
    classical
    exact ss.filter fun t => ¬ sameSequent leq t s

/-- Extend the weakened rules with assumed sequents and their discharge. -/
inductive ProofTree (leq : ExprRel) :
    (Γ Δ : Finset Expr) → Finset Sequent → Type where
  | assume {Γ Δ : Finset Expr} :
      isFSet Γ → isFSet Δ → ProofTree leq Γ Δ {(Γ, Δ)}

  | discharge {Γ Δ α β : Finset Expr} {ss₁ ss₂ : Finset Sequent} :
      ProofTree leq Γ Δ ss₁ →
      ProofTree leq α β ss₂ →
      ProofTree leq Γ Δ (discharged leq ss₁ (α, β) ∪ ss₂)

  | weakening {ss : Finset Sequent} {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ' ->
      isFSet Δ' ->
      ProofTree leq Γ Δ ss ->
      sequentLeq leq Γ Δ Γ' Δ' ->
      ProofTree leq Γ' Δ' ss

  /-- Introduce a sequent whose whole formula is order-equivalent to truth. -/
  | restateTrue {Ω₁ Ω₂ : Finset Expr} :
      isFSet Ω₁ → isFSet Ω₂ →
      isSame leq (sequentToFormula Ω₁ Ω₂) top →
      ProofTree leq Ω₁ Ω₂ ∅

  -- common rules
  | leftFalse : ProofTree leq {bot} ∅ ∅

  | hypothesis {Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      ordContains leq α Ω₁ ->
      ordContains leq α Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ∅

  | cut {ss₁ ss₂ : Finset Sequent} {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- left premise
      ProofTree leq Γ₁ Γ₂ ss₁ ->
      -- right premise
      ProofTree leq Δ₁ Δ₂ ss₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing
      setLeq leq Γ₁ Ω₁ ->
      setLeq leq Δ₂ Ω₂ ->
      -- only α removed
      containedExcept leq Γ₂ Ω₂ (α) ->
      containedExcept leq Δ₁ Ω₁ (α) ->
      ProofTree leq Ω₁ Ω₂ (ss₁ ∪ ss₂)

  -- left structural rules
  | leftAnd {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the right
      setLeq leq Γ₂ Ω₂ ->
      -- only α and β removed on the left
      containedExceptEither leq Γ₁ Ω₁ (α) (β) ->
      -- α ∧ β added on the left
      ordContains leq (and α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ ss

  | leftOr {prems : List Premise}
      {Ω₁ Ω₂ : Finset Expr} :
      -- premises nonempty
      prems ≠ ∅ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- principal formulas well sorted
      (∀ prem ∈ prems,
        let ⟨_, _, φ, _⟩ := prem
        isFormula φ
      ) ->
      -- all premises derivable
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, _⟩ := prem
        ProofTree leq Γ Δ prem.val.2
      ) ->
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, α, _⟩ := prem
        -- all rights preserved
        setLeq leq Δ Ω₂ ∧
        -- all lefts preserved except α
        containedExcept leq Γ Ω₁ (α)
      ) ->
      -- ⋁ᵢ αᵢ added on the left
      ordContains leq (foldFormulas or bot (prems.map (·.val.1))) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ (premiseAssumptions prems)
  | leftImp {ss₁ ss₂ : Finset Sequent} {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- left premise
      ProofTree leq Γ₁ Γ₂ ss₁ ->
      -- right premise
      ProofTree leq Δ₁ Δ₂ ss₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing unnecessary removed
      setLeq leq Γ₁ Ω₁ ->
      setLeq leq Δ₂ Ω₂ ->
      -- only α removed from the first premise right
      containedExcept leq Γ₂ Ω₂ (α) ->
      -- only β removed from the second premise left
      containedExcept leq Δ₁ Ω₁ (β) ->
      -- α => β added on the left
      ordContains leq (imp α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ (ss₁ ∪ ss₂)

  | leftIff {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the right
      setLeq leq Γ₂ Ω₂ ->
      -- only implications removed on the left
      containedExceptEither leq Γ₁ Ω₁ ((imp α β)) ((imp β α)) ->
      -- α <=> β added on the left
      ordContains leq (iff α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ ss

  | leftNot {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing on the left
      setLeq leq Γ₁ Ω₁ ->
      -- only α removed on the right
      containedExcept leq Γ₂ Ω₂ (α) ->
      -- ¬α added on the left
      ordContains leq (neg α) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ ss

  | leftForall {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      isTerm t ->
      -- nothing missing on the right
      setLeq leq Γ₂ Ω₂ ->
      -- only α[t/x] removed on the left
      containedExcept leq Γ₁ Ω₁ ((substOne x t α)) ->
      -- ∀x. α added on the left
      ordContains leq (forall_ x α) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ ss

  | leftExists {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      -- nothing missing on the right
      setLeq leq Γ₂ Ω₂ ->
      -- only α removed on the left
      containedExcept leq Γ₁ Ω₁ (α) ->
      -- ∃x. α added on the left
      ordContains leq (exists_ x α) Ω₁ ->
      -- x not free in conclusion
      x ∉ freeVars (Ω₁ ∪ Ω₂) ->
      ProofTree leq Ω₁ Ω₂ ss

  -- right structural rules

  | rightAnd {prems : List Premise}
      {Ω₁ Ω₂ : Finset Expr} :
      -- premises nonempty
      prems ≠ ∅ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- principal formulas well sorted
      (∀ prem ∈ prems,
        let ⟨_, _, φ, _⟩ := prem
        isFormula φ
      ) ->
      -- all premises derivable
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, _⟩ := prem
        ProofTree leq Γ Δ prem.val.2
      ) ->
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, α, _⟩ := prem
        -- all lefts preserved
        setLeq leq Γ Ω₁ ∧
        -- all rights preserved except α
        containedExcept leq Δ Ω₂ (α)
      ) ->
      -- ⋀ᵢ αᵢ added on the right
      ordContains leq (foldFormulas and top (prems.map (·.val.1))) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ (premiseAssumptions prems)
  | rightOr {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the left
      setLeq leq Γ₁ Ω₁ ->
      -- only α and β removed on the right
      containedExceptEither leq Γ₂ Ω₂ (α) (β) ->
      -- α ∨ β added on the right
      ordContains leq (or α β) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightImp {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- only α removed on the left
      containedExcept leq Γ₁ Ω₁ (α) ->
      -- only β removed on the right
      containedExcept leq Γ₂ Ω₂ (β) ->
      -- α => β added on the right
      ordContains leq (imp α β) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightIff {ss₁ ss₂ : Finset Sequent} {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- left premise
      ProofTree leq Γ₁ Γ₂ ss₁ ->
      -- right premise
      ProofTree leq Δ₁ Δ₂ ss₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the left
      setLeq leq Γ₁ Ω₁ ->
      setLeq leq Δ₁ Ω₁ ->
      -- only implications removed on the right
      containedExcept leq Γ₂ Ω₂ ((imp α β)) ->
      containedExcept leq Δ₂ Ω₂ ((imp β α)) ->
      -- α <=> β added on the right
      ordContains leq (iff α β) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ (ss₁ ∪ ss₂)

  | rightNot {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing on the right
      setLeq leq Γ₂ Ω₂ ->
      -- only α removed on the left
      containedExcept leq Γ₁ Ω₁ (α) ->
      -- ¬α added on the right
      ordContains leq (neg α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightForall {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      -- nothing missing on the left
      setLeq leq Γ₁ Ω₁ ->
      -- only α removed on the right
      containedExcept leq Γ₂ Ω₂ (α) ->
      -- ∀x. α added on the right
      ordContains leq (forall_ x α) Ω₂ ->
      -- x not free in conclusion
      x ∉ freeVars (Ω₁ ∪ Ω₂) ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightExists {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      isTerm t ->
      -- nothing missing on the left
      setLeq leq Γ₁ Ω₁ ->
      -- only α[t/x] removed on the right
      containedExcept leq Γ₂ Ω₂ ((substOne x t α)) ->
      -- ∃x. α added on the right
      ordContains leq (exists_ x α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightEpsilon {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      x.sort = ind ->
      isFormula α ->
      isTerm t ->
      -- nothing missing on the left
      setLeq leq Γ₁ Ω₁ ->
      -- only α[t/x] removed on the right
      containedExcept leq Γ₂ Ω₂ ((substOne x t α)) ->
      -- ε instantiation added on the right
      ordContains leq (substOne x (epsilon_ (.lam x α)) α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ss

  -- equality rules

  | leftRefl {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (s t : Expr) :
      -- premise
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- reflexive term
      isTerm s -> isTerm t ->
      isSame leq s t ->
      -- right preserved
      setLeq leq Γ₂ Ω₂ ->
      -- only the reflexive equality removed on the left
      containedExcept leq Γ₁ Ω₁ ((eq s t)) ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightRefl {Ω₁ Ω₂ : Finset Expr} (s t : Expr) :
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- reflexive term
      isTerm s -> isTerm t ->
      isSame leq s t ->
      -- the reflexive equality added on the right
      ordContains leq (eq s t) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ∅

  /-- Both premises contribute imported assumptions; freshness concerns Θ and Ξ. -/
  | leftSubst {ss₀ ss₁ : Finset Sequent} {Γ₁ Γ₂ Θ Ξ Ω₁ Ω₂ : Finset Expr} (r : SubstRule) :
      ProofTree leq Γ₁ Γ₂ ss₀ -> ProofTree leq Θ (insert r.equation Ξ) ss₁ ->
      isFSet Ω₁ -> isFSet Ω₂ -> r.valid -> r.fresh Θ Ξ ->
      containedExcept leq Γ₁ Ω₁ r.source -> setLeq leq Γ₂ Ω₂ ->
      ordContains leq r.target Ω₁ -> setLeq leq Θ Ω₁ -> setLeq leq Ξ Ω₂ ->
      ProofTree leq Ω₁ Ω₂ (ss₀ ∪ ss₁)

  | rightSubst {ss₀ ss₁ : Finset Sequent} {Γ₁ Γ₂ Θ Ξ Ω₁ Ω₂ : Finset Expr} (r : SubstRule) :
      ProofTree leq Γ₁ Γ₂ ss₀ -> ProofTree leq Θ (insert r.equation Ξ) ss₁ ->
      isFSet Ω₁ -> isFSet Ω₂ -> r.valid -> r.fresh Θ Ξ ->
      setLeq leq Γ₁ Ω₁ -> containedExcept leq Γ₂ Ω₂ r.source ->
      ordContains leq r.target Ω₂ -> setLeq leq Θ Ω₁ -> setLeq leq Ξ Ω₂ ->
      ProofTree leq Ω₁ Ω₂ (ss₀ ∪ ss₁)

  | instSchema {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (σ : Subst) :
      ProofTree leq Γ₁ Γ₂ ss ->
      isFSet Ω₁ -> isFSet Ω₂ ->
      Subst.wellSorted σ ->
      -- Preserve each instantiated formula on its original side.
      (
        let Γ₁' := Γ₁.image (Subst.subst σ)
        let Γ₂' := Γ₂.image (Subst.subst σ)

        setLeq leq Γ₁' Ω₁ ∧ setLeq leq Γ₂' Ω₂
      ) ->
      ProofTree leq Ω₁ Ω₂ ss

end Imported
