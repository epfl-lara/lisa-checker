import Lisa.LambdaFol.EliminateInstantiation.InstantiateReplacement
/-!
# Schematic instantiation is admissible in WithoutInstantiation

The induction is generalized over simultaneous substitutions. At an eigenrule we
choose a fresh name and override that variable's image in the induction hypothesis. Thus instantiating a schematic symbol can introduce arbitrary free
variables without violating the quantifier side conditions.

Assumptions are carried in the antecedent and are instantiated too.
-/

namespace Lisa.LambdaFol.WithoutInstantiation

open Expr Instantiation

noncomputable def ProofTree.instantiate {Γ Δ : Finset Formula}
    (d : ProofTree Γ Δ) (σ : Instantiation) :
    ProofTree (σ.formulaSet Γ) (σ.formulaSet Δ) := by
  induction d generalizing σ with
  | hypothesis p => simpa using ProofTree.hypothesis (σ.applyClass p)
  | weakening _ hΓ hΔ ih => exact .weakening (ih σ) (σ.formulaSet_mono hΓ) (σ.formulaSet_mono hΔ)
  | cut p _ _ ih₁ ih₂ =>
      simpa using ProofTree.cut (σ.applyClass p) (by simpa using ih₁ σ) (by simpa using ih₂ σ)
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
      rw [Instantiation.formulaSet_insert, σ.applyClass_forall x y hy p hx hp hf]
      apply ProofTree.leftForall y ((σ.renameBinder x y hy).apply p) (σ.apply t)
        (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp) (σ.hasSort ht)
      simpa only [Instantiation.formulaSet_insert, σ.applyClass_substOne x y hy p t hx hp ht hf] using ih σ
  | @rightForall Γ Δ x p hx hp _ hΓ hΔ ih =>
      obtain ⟨y, hy, hb, hyΓ, hyΔ⟩ := σ.freshEigenvariable x.sort p Γ Δ
      rw [Instantiation.formulaSet_insert, σ.applyClass_forall x y hy p hx hp hb]
      apply ProofTree.rightForall y ((σ.renameBinder x y hy).apply p) (hy.trans hx)
        ((σ.renameBinder x y hy).hasSort hp)
      · simpa only [Instantiation.formulaSet_insert, applyClass_ofExpr,
          σ.formulaSet_renameBinder x y hy hΓ, σ.formulaSet_renameBinder x y hy hΔ] using
          ih (σ.renameBinder x y hy)
      · exact hyΓ
      · exact hyΔ
  | @leftExists Γ Δ x p hx hp _ hΓ hΔ ih =>
      obtain ⟨y, hy, hb, hyΓ, hyΔ⟩ := σ.freshEigenvariable x.sort p Γ Δ
      rw [Instantiation.formulaSet_insert, σ.applyClass_exists x y hy p hx hp hb]
      apply ProofTree.leftExists y ((σ.renameBinder x y hy).apply p) (hy.trans hx)
        ((σ.renameBinder x y hy).hasSort hp)
      · simpa only [Instantiation.formulaSet_insert, applyClass_ofExpr,
          σ.formulaSet_renameBinder x y hy hΓ, σ.formulaSet_renameBinder x y hy hΔ] using
          ih (σ.renameBinder x y hy)
      · exact hyΓ
      · exact hyΔ
  | rightExists x p t hx hp ht _ ih =>
      obtain ⟨y, hy, hf⟩ := fresh x.sort (σ.substitution.rangeFreeVars ∪ p.freeVars)
      rw [Instantiation.formulaSet_insert, σ.applyClass_exists x y hy p hx hp hf]
      apply ProofTree.rightExists y ((σ.renameBinder x y hy).apply p) (σ.apply t)
        (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp) (σ.hasSort ht)
      simpa only [Instantiation.formulaSet_insert, σ.applyClass_substOne x y hy p t hx hp ht hf] using ih σ
  | refl t ht => simpa using ProofTree.refl (σ.apply t) (σ.hasSort ht)
  | rightEpsilon x p t hx hp ht _ ih =>
      obtain ⟨y, hy, hf⟩ := fresh x.sort (σ.substitution.rangeFreeVars ∪ p.freeVars)
      rw [Instantiation.formulaSet_insert, σ.applyClass_epsilon_subst x y hy p hx hp hf]
      apply ProofTree.rightEpsilon y ((σ.renameBinder x y hy).apply p) (σ.apply t)
        (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp) (σ.hasSort ht)
      simpa only [Instantiation.formulaSet_insert, σ.applyClass_substOne x y hy p t hx hp ht hf] using ih σ
  | @leftReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂
  | @rightReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂ =>
      let replacement := instantiateReplacement σ r hr hf
        (fun τ => by simpa only [Instantiation.formulaSet_insert] using ih₂ τ)
      first
      | simpa only [Instantiation.formulaSet_insert, Instantiation.formulaSet_union, replacement.target_eq] using
          ProofTree.leftReplace (Γ := σ.formulaSet Γ) (Δ := σ.formulaSet Δ)
            replacement.rule replacement.valid replacement.fresh
            (by simpa only [Instantiation.formulaSet_insert, replacement.source_eq] using ih₁ σ) replacement.comparison
      | simpa only [Instantiation.formulaSet_insert, Instantiation.formulaSet_union, replacement.target_eq] using
          ProofTree.rightReplace (Γ := σ.formulaSet Γ) (Δ := σ.formulaSet Δ)
            replacement.rule replacement.valid replacement.fresh
            (by simpa only [Instantiation.formulaSet_insert, replacement.source_eq] using ih₁ σ) replacement.comparison

theorem Provable.instantiate {Γ Δ : Finset Formula} (h : Provable Γ Δ) (σ : Instantiation) :
    Provable (σ.formulaSet Γ) (σ.formulaSet Δ) := by
  obtain ⟨d⟩ := h
  exact ⟨d.instantiate σ⟩

end Lisa.LambdaFol.WithoutInstantiation
