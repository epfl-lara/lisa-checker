import Lisa.SCLambdaToPure.OrderedToA.InstantiateReplacement
/-!
# Schematic instantiation is admissible in A

The induction is generalized over simultaneous substitutions. At an eigenrule we
choose a fresh name and override that variable's image in the induction hypothesis. Thus instantiating a schematic symbol can introduce arbitrary free
variables without violating the quantifier side conditions.

Assumptions are carried in the antecedent and are instantiated too.
-/

namespace Lisa.SCLambdaToPure.A

open Expr Instantiation

noncomputable def ProofTree.instantiate {Γ Δ : Context}
    (d : ProofTree Γ Δ) (σ : Instantiation) :
    ProofTree (σ.context Γ) (σ.context Δ) := by
  induction d generalizing σ with
  | hypothesis p => simpa using ProofTree.hypothesis (σ.expression p)
  | weakening _ hΓ hΔ ih => exact .weakening (ih σ) (σ.context_mono hΓ) (σ.context_mono hΔ)
  | cut p _ _ ih₁ ih₂ =>
      simpa using ProofTree.cut (σ.expression p) (by simpa using ih₁ σ) (by simpa using ih₂ σ)
  | leftFalse => simpa using (ProofTree.leftFalse)
  | rightTrue => simpa using (ProofTree.rightTrue)
  | leftAnd p q hp hq _ ih =>
      simpa using ProofTree.leftAnd (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih σ)
  | rightAnd p q hp hq _ _ ih₁ ih₂ =>
      simpa using ProofTree.rightAnd (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih₁ σ) (by simpa using ih₂ σ)
  | leftOr p q hp hq _ _ ih₁ ih₂ =>
      simpa using ProofTree.leftOr (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih₁ σ) (by simpa using ih₂ σ)
  | rightOr p q hp hq _ ih =>
      simpa using ProofTree.rightOr (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih σ)
  | leftImp p q hp hq _ _ ih₁ ih₂ =>
      simpa using ProofTree.leftImp (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih₁ σ) (by simpa using ih₂ σ)
  | rightImp p q hp hq _ ih =>
      simpa using ProofTree.rightImp (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih σ)
  | leftIff p q hp hq _ ih =>
      simpa using ProofTree.leftIff (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih σ)
  | rightIff p q hp hq _ _ ih₁ ih₂ =>
      simpa using ProofTree.rightIff (σ.apply p) (σ.apply q) (σ.hasSort hp) (σ.hasSort hq)
        (by simpa using ih₁ σ) (by simpa using ih₂ σ)
  | leftNot p hp _ ih =>
      simpa using ProofTree.leftNot (σ.apply p) (σ.hasSort hp) (by simpa using ih σ)
  | rightNot p hp _ ih =>
      simpa using ProofTree.rightNot (σ.apply p) (σ.hasSort hp) (by simpa using ih σ)
  | leftForall x p t hx hp ht _ ih =>
      obtain ⟨y, hy, hf⟩ := fresh x.sort (σ.substitution.rangeFreeVars ∪ p.freeVars)
      rw [Instantiation.context_insert, σ.expression_forall x y hy p hx hp hf]
      apply ProofTree.leftForall y ((σ.renameBinder x y hy).apply p) (σ.apply t)
        (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp) (σ.hasSort ht)
      simpa only [Instantiation.context_insert, σ.expression_substOne x y hy p t hx hp ht hf] using ih σ
  | @rightForall Γ Δ x p hx hp _ hΓ hΔ ih =>
      obtain ⟨y, hy, hf⟩ := fresh x.sort
        ((σ.substitution.rangeFreeVars ∪ p.freeVars) ∪ support (σ.context Γ) ∪ support (σ.context Δ))
      have hb : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars :=
        fun h => hf (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      rw [Instantiation.context_insert, σ.expression_forall x y hy p hx hp hb]
      apply ProofTree.rightForall y ((σ.renameBinder x y hy).apply p) (hy.trans hx)
        ((σ.renameBinder x y hy).hasSort hp)
      · simpa only [Instantiation.context_insert, expression_ofExpr,
          σ.context_renameBinder x y hy hΓ, σ.context_renameBinder x y hy hΔ] using
          ih (σ.renameBinder x y hy)
      · exact fresh_of_not_mem_support (fun h => hf (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      · exact fresh_of_not_mem_support (fun h => hf (Finset.mem_union_right _ h))
  | @leftExists Γ Δ x p hx hp _ hΓ hΔ ih =>
      obtain ⟨y, hy, hf⟩ := fresh x.sort
        ((σ.substitution.rangeFreeVars ∪ p.freeVars) ∪ support (σ.context Γ) ∪ support (σ.context Δ))
      have hb : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars :=
        fun h => hf (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      rw [Instantiation.context_insert, σ.expression_exists x y hy p hx hp hb]
      apply ProofTree.leftExists y ((σ.renameBinder x y hy).apply p) (hy.trans hx)
        ((σ.renameBinder x y hy).hasSort hp)
      · simpa only [Instantiation.context_insert, expression_ofExpr,
          σ.context_renameBinder x y hy hΓ, σ.context_renameBinder x y hy hΔ] using
          ih (σ.renameBinder x y hy)
      · exact fresh_of_not_mem_support (fun h => hf (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      · exact fresh_of_not_mem_support (fun h => hf (Finset.mem_union_right _ h))
  | rightExists x p t hx hp ht _ ih =>
      obtain ⟨y, hy, hf⟩ := fresh x.sort (σ.substitution.rangeFreeVars ∪ p.freeVars)
      rw [Instantiation.context_insert, σ.expression_exists x y hy p hx hp hf]
      apply ProofTree.rightExists y ((σ.renameBinder x y hy).apply p) (σ.apply t)
        (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp) (σ.hasSort ht)
      simpa only [Instantiation.context_insert, σ.expression_substOne x y hy p t hx hp ht hf] using ih σ
  | refl t ht => simpa using ProofTree.refl (σ.apply t) (σ.hasSort ht)
  | rightEpsilon x p t hx hp ht _ ih =>
      obtain ⟨y, hy, hf⟩ := fresh x.sort (σ.substitution.rangeFreeVars ∪ p.freeVars)
      rw [Instantiation.context_insert, σ.expression_epsilon_subst x y hy p hx hp hf]
      apply ProofTree.rightEpsilon y ((σ.renameBinder x y hy).apply p) (σ.apply t)
        (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp) (σ.hasSort ht)
      simpa only [Instantiation.context_insert, σ.expression_substOne x y hy p t hx hp ht hf] using ih σ
  | @leftReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂
  | @rightReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂ =>
      let avoid := ruleAvoid σ r Θ Ξ
      let ρ := freshParameters avoid
      have hs := freshParameters_sort avoid
      have hinj := freshParameters_injective avoid
      have hctx := fun x (_ : x ∈ r.context.params) => ruleAvoid_context σ r Θ Ξ x
      have hcmp := fun c (hc : c ∈ r.comparisons) x (_ : x ∈ c.2) => ruleAvoid_comparison σ r Θ Ξ c hc x
      have hv := mapRule_valid σ ρ hinj hs r hr hctx hcmp
      have hf' : RuleFresh (mapRule σ ρ hs r) (σ.context Θ) (σ.context Ξ) := by
        intro c hc x hx
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact ruleAvoid_fresh σ r Θ Ξ y
      have hsource : ofExpr (mapRule σ ρ hs r).source hv.2.2.2.1 =
          σ.expression (ofExpr r.source hr.2.2.2.1) := by
        rw [expression_ofExpr]; exact (ofExpr_eq _ _).mpr (.alpha (mapRule_source σ ρ hinj hs r hr hctx))
      have htarget : ofExpr (mapRule σ ρ hs r).target hv.2.2.2.2 =
          σ.expression (ofExpr r.target hr.2.2.2.2) := by
        rw [expression_ofExpr]; exact (ofExpr_eq _ _).mpr (.alpha (mapRule_target σ ρ hinj hs r hr hctx))
      have de := ProofTree.instantiateEquation σ ρ hs r hr hv hf (fun τ => by simpa only [Instantiation.context_insert] using ih₂ τ)
      first
      | simpa only [Instantiation.context_insert, Instantiation.context_union, htarget] using
          ProofTree.leftReplace (Γ := σ.context Γ) (Δ := σ.context Δ)
            (mapRule σ ρ hs r) hv hf'
            (by simpa only [Instantiation.context_insert, hsource] using ih₁ σ) de
      | simpa only [Instantiation.context_insert, Instantiation.context_union, htarget] using
          ProofTree.rightReplace (Γ := σ.context Γ) (Δ := σ.context Δ)
            (mapRule σ ρ hs r) hv hf'
            (by simpa only [Instantiation.context_insert, hsource] using ih₁ σ) de

theorem Provable.instantiate {Γ Δ : Context} (h : Provable Γ Δ) (σ : Instantiation) :
    Provable (σ.context Γ) (σ.context Δ) := by
  obtain ⟨d⟩ := h
  exact ⟨d.instantiate σ⟩

end Lisa.SCLambdaToPure.A
