import Lisa.SCLambdaToPure.OrderedToA.SequentEncoding
/-! Ordered at αβη equivalence becomes system B by passing to formula classes.
Its restatement rule is derived through sequent packing and unpacking. -/
noncomputable section
namespace Lisa.SCLambdaToPure.B
open Expr A

private theorem fresh_context {x : SVar} {Γ Δ : Finset Expr}
    (hΓ : isFSet Γ) (h : x ∉ freeVars Δ) (hsub : Γ ⊆ Δ) : Fresh x (A.context Γ hΓ) :=
  fresh_of_representatives x Γ hΓ (fun e he hx => h (Finset.mem_biUnion.mpr ⟨e, hsub he, hx⟩))

private theorem rule_fresh {r : SubstRule} {Θ Ξ : Finset Expr}
    (hΘ : isFSet Θ) (hΞ : isFSet Ξ) (h : r.fresh Θ Ξ) :
    RuleFresh r (A.context Θ hΘ) (A.context Ξ hΞ) := by
  intro c hc x hx
  exact ⟨fresh_context hΘ (h c hc x hx) Finset.subset_union_left,
    fresh_context hΞ (h c hc x hx) Finset.subset_union_right⟩

def ofOrdered {Γ Δ : Finset Expr} (d : Ordered.ProofTree AlphaBetaEta Γ Δ) :
    ∀ (hΓ : isFSet Γ) (hΔ : isFSet Δ), ProofTree (A.context Γ hΓ) (A.context Δ hΔ) := by
  induction d with
  | restateWeaken hΓ hΔ hΓ' hΔ' _ h ih =>
      intro _ _; exact restate hΓ hΔ hΓ' hΔ' h (ih hΓ hΔ)
  | weakening hΓ hΔ hΓ' hΔ' _ hleft hright ih =>
      intro _ _; exact .weakening (ih hΓ hΔ) (A.context_mono hΓ hΓ' hleft) (A.context_mono hΔ hΔ' hright)
  | hypothesis p hp => intro _ _; simpa using ProofTree.hypothesis (ofExpr p hp)
  | rightTrue => intro _ _; simpa using (ProofTree.rightTrue)
  | leftFalse => intro _ _; simpa using (ProofTree.leftFalse)
  | cut p hΓ hΔ hΘ hΞ hp _ _ ih₁ ih₂ =>
      intro _ _
      simpa using ProofTree.cut (ofExpr p hp)
        (by simpa using ih₁ hΓ (isFSet_insert hp hΔ))
        (by simpa using ih₂ (isFSet_insert hp hΘ) hΞ)
  | leftAnd p q hΓ hΔ hp hq _ ih =>
      intro _ _; simpa using ProofTree.leftAnd p q hp hq
        (by simpa using ih (isFSet_insert hp (isFSet_insert hq hΓ)) hΔ)
  | rightOr p q hΓ hΔ hp hq _ ih =>
      intro _ _; simpa using ProofTree.rightOr p q hp hq
        (by simpa using ih hΓ (isFSet_insert hp (isFSet_insert hq hΔ)))
  | rightImp p q hΓ hΔ hp hq _ ih =>
      intro _ _; simpa using ProofTree.rightImp p q hp hq
        (by simpa using ih (isFSet_insert hp hΓ) (isFSet_insert hq hΔ))
  | leftIff p q hΓ hΔ hp hq _ ih =>
      intro _ _; simpa using ProofTree.leftIff p q hp hq
        (by simpa using ih (isFSet_insert (isFormula_imp hp hq) (isFSet_insert (isFormula_imp hq hp) hΓ)) hΔ)
  | leftNot p hΓ hΔ hp _ ih =>
      intro _ _; simpa using ProofTree.leftNot p hp (by simpa using ih hΓ (isFSet_insert hp hΔ))
  | rightNot p hΓ hΔ hp _ ih =>
      intro _ _; simpa using ProofTree.rightNot p hp (by simpa using ih (isFSet_insert hp hΓ) hΔ)
  | rightAnd p q hΓ hΔ hΘ hΞ hp hq _ _ ih₁ ih₂ =>
      intro _ _; simpa using ProofTree.rightAnd p q hp hq
        (by simpa using ih₁ hΓ (isFSet_insert hp hΔ)) (by simpa using ih₂ hΘ (isFSet_insert hq hΞ))
  | leftOr p q hΓ hΔ hΘ hΞ hp hq _ _ ih₁ ih₂ =>
      intro _ _; simpa using ProofTree.leftOr p q hp hq
        (by simpa using ih₁ (isFSet_insert hp hΓ) hΔ) (by simpa using ih₂ (isFSet_insert hq hΘ) hΞ)
  | leftImp p q hΓ hΔ hΘ hΞ hp hq _ _ ih₁ ih₂ =>
      intro _ _; simpa using ProofTree.leftImp p q hp hq
        (by simpa using ih₁ hΓ (isFSet_insert hp hΔ)) (by simpa using ih₂ (isFSet_insert hq hΘ) hΞ)
  | rightIff p q hΓ hΔ hΘ hΞ hp hq _ _ ih₁ ih₂ =>
      intro _ _; simpa using ProofTree.rightIff p q hp hq
        (by simpa using ih₁ hΓ (isFSet_insert (isFormula_imp hp hq) hΔ))
        (by simpa using ih₂ hΘ (isFSet_insert (isFormula_imp hq hp) hΞ))
  | leftForall x p t hΓ hΔ hx hp ht _ ih =>
      intro _ _; simpa using ProofTree.leftForall x p t hx hp ht
        (by simpa using ih (isFSet_insert (isFormula_substOne hx ht hp) hΓ) hΔ)
  | rightExists x p t hΓ hΔ hx hp ht _ ih =>
      intro _ _; simpa using ProofTree.rightExists x p t hx hp ht
        (by simpa using ih hΓ (isFSet_insert (isFormula_substOne hx ht hp) hΔ))
  | rightForall x p hΓ hΔ hx hp _ hf ih =>
      intro _ _; simpa using ProofTree.rightForall x p hx hp
        (by simpa using ih hΓ (isFSet_insert hp hΔ))
        (fresh_context hΓ hf (by intro e he; simp [he]))
        (fresh_context hΔ hf (by intro e he; simp [he]))
  | leftExists x p hΓ hΔ hx hp _ hf ih =>
      intro _ _; simpa using ProofTree.leftExists x p hx hp
        (by simpa using ih (isFSet_insert hp hΓ) hΔ)
        (fresh_context hΓ hf (by intro e he; simp [he]))
        (fresh_context hΔ hf (by intro e he; simp [he]))
  | rightEpsilon x p t hΓ hΔ hx hp ht _ ih =>
      intro _ _; simpa using ProofTree.rightEpsilon x p t hx hp ht
        (by simpa using ih hΓ (isFSet_insert (isFormula_substOne hx ht hp) hΔ))
  | rightRefl t ht => intro _ _; simpa using ProofTree.refl t ht
  | leftRefl t hΓ hΔ ht _ ih =>
      intro _ _
      simpa using ProofTree.cut (Γ := ∅) (Δ := ∅) (ofExpr (eq t t) (isFormula_eq ht ht))
        (.refl t ht) (by simpa using ih (isFSet_insert (isFormula_eq ht ht) hΓ) hΔ)
  | leftSubst r hΓ hΔ hΘ hΞ hr hf _ _ ih₁ ih₂ =>
      intro _ _; simpa using ProofTree.leftReplace r hr (rule_fresh hΘ hΞ hf)
        (by simpa using ih₁ (isFSet_insert hr.2.2.2.1 hΓ) hΔ)
        (by simpa using ih₂ hΘ (isFSet_insert (SubstRule.equation_isFormula hr) hΞ))
  | rightSubst r hΓ hΔ hΘ hΞ hr hf _ _ ih₁ ih₂ =>
      intro _ _; simpa using ProofTree.rightReplace r hr (rule_fresh hΘ hΞ hf)
        (by simpa using ih₁ hΓ (isFSet_insert hr.2.2.2.1 hΔ))
        (by simpa using ih₂ hΘ (isFSet_insert (SubstRule.equation_isFormula hr) hΞ))
  | @instSchema Γ Δ σ hΓ hΔ hs _ ih =>
      intro hΓ' hΔ'
      let τ : Instantiation := ⟨σ, hs⟩
      change ProofTree (A.context (Γ.image τ.apply) hΓ') (A.context (Δ.image τ.apply) hΔ')
      rw [A.context_image τ _ hΓ hΓ', A.context_image τ _ hΔ hΔ']
      exact .instSchema τ (ih hΓ hΔ)

end Lisa.SCLambdaToPure.B
