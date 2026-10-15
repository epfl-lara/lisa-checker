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
noncomputable def sameSequent (leq : Order) (s t : Sequent) : Prop :=
  sequentLeq leq s.1 s.2 t.1 t.2 ∧ sequentLeq leq t.1 t.2 s.1 s.2

/-- Remove every assumption equivalent to the justification's conclusion. -/
noncomputable def discharged (leq : Order) (ss : Finset Sequent) (s : Sequent) :
    Finset Sequent :=
  by
    classical
    exact ss.filter fun t => ¬ sameSequent leq t s

/-- Extend the weakened rules with assumed sequents and their discharge. -/
inductive ProofTree (leq : Order) [OrderReduction leq] :
    (Γ Δ : Finset Expr) → Finset Sequent → Type where
  | assume {Γ Δ : Finset Expr} :
      isFSet Γ → isFSet Δ → ProofTree leq Γ Δ {(Γ, Δ)}

  | discharge {Γ Δ α β : Finset Expr} {ss₁ ss₂ : Finset Sequent} :
      ProofTree leq Γ Δ ss₁ →
      ProofTree leq α β ss₂ →
      ProofTree leq Γ Δ (discharged leq ss₁ (α, β) ∪ ss₂)

  | restate {ss : Finset Sequent} {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ ->
      isFSet Δ ->
      isFSet Γ' ->
      isFSet Δ' ->
      ProofTree leq Γ Δ ss ->
      sequentLeq leq Γ Δ Γ' Δ' ->
      sequentLeq leq Γ' Δ' Γ Δ ->
      ProofTree leq Γ' Δ' ss

  | weakening {ss : Finset Sequent} {Γ Δ Γ' Δ' : Finset Expr} :
      isFSet Γ ->
      isFSet Δ ->
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
  | hypothesis {Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      ordContains leq α Ω₁ ->
      ordContains leq α Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ∅

  | cut {ss₁ ss₂ : Finset Sequent} {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- left premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss₁ ->
      -- right premise
      isFSet Δ₁ -> isFSet Δ₂ ->
      ProofTree leq Δ₁ Δ₂ ss₂ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing
      reducedSubset leq Γ₁ Ω₁ ->
      reducedSubset leq Δ₂ Ω₂ ->
      -- only α removed
      containedExcept leq Γ₂ Ω₂ (α) ->
      containedExcept leq Δ₁ Ω₁ (α) ->
      ProofTree leq Ω₁ Ω₂ (ss₁ ∪ ss₂)

  -- left structural rules
  | leftAnd {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the right
      reducedSubset leq Γ₂ Ω₂ ->
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
      -- all premises well sorted
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, φ, _⟩ := prem
        isFSet Γ ∧ isFSet Δ ∧ isFormula φ
      ) ->
      -- all premises derivable
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, _⟩ := prem
        ProofTree leq Γ Δ prem.val.2
      ) ->
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, α, _⟩ := prem
        -- all rights preserved
        reducedSubset leq Δ Ω₂ ∧
        -- all lefts preserved except α
        containedExcept leq Γ Ω₁ (α)
      ) ->
      -- ⋁ᵢ αᵢ added on the left
      (
        let disjuncts := prems.map (·.val.1)
        let disjunction :=
          match disjuncts with
          | [] => bot -- unreachable case
          | α :: βs => βs.foldl Expr.or α

        ordContains leq disjunction Ω₁
      ) ->
      ProofTree leq Ω₁ Ω₂ (premiseAssumptions prems)
  | leftImp {ss₁ ss₂ : Finset Sequent} {Γ₁ Γ₂ Δ₁ Δ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- left premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss₁ ->
      -- right premise
      isFSet Δ₁ -> isFSet Δ₂ ->
      ProofTree leq Δ₁ Δ₂ ss₂ ->
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
      ProofTree leq Ω₁ Ω₂ (ss₁ ∪ ss₂)

  | leftIff {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the right
      reducedSubset leq Γ₂ Ω₂ ->
      -- only implications removed on the left
      containedExceptEither leq Γ₁ Ω₁ ((imp α β)) ((imp β α)) ->
      -- α <=> β added on the left
      ordContains leq (iff α β) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ ss

  | leftNot {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing on the left
      reducedSubset leq Γ₁ Ω₁ ->
      -- only α removed on the right
      containedExcept leq Γ₂ Ω₂ (α) ->
      -- ¬α added on the left
      ordContains leq (neg α) Ω₁ ->
      ProofTree leq Ω₁ Ω₂ ss

  | leftForall {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
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
      ProofTree leq Ω₁ Ω₂ ss

  | leftExists {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
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
      ProofTree leq Ω₁ Ω₂ ss

  -- right structural rules

  | rightAnd {prems : List Premise}
      {Ω₁ Ω₂ : Finset Expr} :
      -- premises nonempty
      prems ≠ ∅ ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- all premises well sorted
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, φ, _⟩ := prem
        isFSet Γ ∧ isFSet Δ ∧ isFormula φ
      ) ->
      -- all premises derivable
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, _⟩ := prem
        ProofTree leq Γ Δ prem.val.2
      ) ->
      (∀ prem ∈ prems,
        let ⟨Γ, Δ, α, _⟩ := prem
        -- all lefts preserved
        reducedSubset leq Γ Ω₁ ∧
        -- all rights preserved except α
        containedExcept leq Δ Ω₂ (α)
      ) ->
      -- ⋀ᵢ αᵢ added on the right
      (
        let conjuncts := prems.map (·.val.1)
        let conjunction :=
          match conjuncts with
          | [] => top -- unreachable case
          | α :: βs => βs.foldl Expr.and α

        ordContains leq conjunction Ω₂
      ) ->
      ProofTree leq Ω₁ Ω₂ (premiseAssumptions prems)
  | rightOr {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α -> isFormula β ->
      -- nothing missing on the left
      reducedSubset leq Γ₁ Ω₁ ->
      -- only α and β removed on the right
      containedExceptEither leq Γ₂ Ω₂ (α) (β) ->
      -- α ∨ β added on the right
      ordContains leq (or α β) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightImp {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α β : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
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
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss₁ ->
      -- right premise
      isFSet Δ₁ -> isFSet Δ₂ ->
      ProofTree leq Δ₁ Δ₂ ss₂ ->
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
      ProofTree leq Ω₁ Ω₂ (ss₁ ∪ ss₂)

  | rightNot {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      isFormula α ->
      -- nothing missing on the right
      reducedSubset leq Γ₂ Ω₂ ->
      -- only α removed on the left
      containedExcept leq Γ₁ Ω₁ (α) ->
      -- ¬α added on the right
      ordContains leq (neg α) Ω₂ ->
      ProofTree leq Ω₁ Ω₂ ss

  | rightForall {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
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
      ProofTree leq Ω₁ Ω₂ ss

  | rightExists {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
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
      ProofTree leq Ω₁ Ω₂ ss

  | rightEpsilon {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (x : SVar) (α t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
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
      ProofTree leq Ω₁ Ω₂ ss

  -- equality rules

  | leftRefl {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (s t : Expr) :
      -- premise
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
      -- conclusion
      isFSet Ω₁ -> isFSet Ω₂ ->
      -- reflexive term
      isTerm s -> isTerm t ->
      isSame leq s t ->
      -- right preserved
      reducedSubset leq Γ₂ Ω₂ ->
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

  | leftSubstEq {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂: Finset Expr} (eqs : List SubstPair) (φ : SubstContext) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
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
      ProofTree leq Ω₁ Ω₂ ss

  | rightSubstEq {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (eqs : List SubstPair) (φ : SubstContext) :
      isFSet Γ₁ -> isFSet Γ₂ ->
      ProofTree leq Γ₁ Γ₂ ss ->
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
      ProofTree leq Ω₁ Ω₂ ss

  | instSchema {ss : Finset Sequent} {Γ₁ Γ₂ Ω₁ Ω₂ : Finset Expr} (σ : Subst) :
      isFSet Γ₁ -> isFSet Γ₂ ->
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
