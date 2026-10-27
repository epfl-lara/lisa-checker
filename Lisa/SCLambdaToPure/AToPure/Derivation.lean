import Lisa.SCLambdaToPure.AToPure.FormulaClasses
import Lisa.SCLambdaToPure.AToPure.ReplacementRule
import Lisa.SCLambdaToPure.AToPure.Translation

/-! System A translates by grounding, normalization, and first-order readback.
There is no schematic-instantiation case: B → A has already removed those nodes.
All intermediate formulas remain unrestricted.

The induction works for any assignment fixing the admitted constants. In the
eigenvariable cases it changes the assignment to a fresh target variable;
in the replacement cases it uses `substitution_rule_equiv_contexts`.
`A.Provable.toPure` later selects grounding and recovers the original conclusion. -/
namespace Lisa.SCLambdaToPure.A

open Syntactic

/-- Translate A under any assignment of schematic symbols to sorted expressions
of the first-order epsilon fragment. This is a syntactic assignment, not a model. -/
theorem toPure {Γ Δ : A.Context} (d : A.ProofTree Γ Δ) :
    ∀ R : Assignment, R.FixesConstants →
      Pure.Provable (R.classContext Γ) (R.classContext Δ) := by
  induction d with
  | weakening _ hΓ hΔ ih =>
      intro R hR
      obtain ⟨d⟩ := ih R hR
      exact ⟨d.weakening (Finset.image_mono R.formulaClass hΓ) (Finset.image_mono R.formulaClass hΔ)⟩
  | rightTrue =>
      intro R hR
      exact ⟨by simpa [R.formula_top hR] using (Pure.ProofTree.rightTrue (L := Readback.language))⟩
  | leftFalse =>
      intro R hR
      exact ⟨by simpa [R.formula_bot hR] using (Pure.ProofTree.leftFalse (L := Readback.language))⟩
  | hypothesis p =>
      intro R _
      exact ⟨by simpa using Pure.ProofTree.hypothesis (R.formulaClass p)⟩
  | cut p _ _ ih₁ ih₂ =>
      intro R hR
      obtain ⟨d₁⟩ := ih₁ R hR
      obtain ⟨d₂⟩ := ih₂ R hR
      exact ⟨by
        simpa using Pure.ProofTree.cut (R.formulaClass p)
          (by simpa using d₁) (by simpa using d₂)⟩
  | leftAnd p q hp hq _ ih =>
      intro R hR
      obtain ⟨d⟩ := ih R hR
      exact ⟨by
        simpa [R.formula_and hR hp hq] using Pure.ProofTree.leftAnd (R.formula p) (R.formula q)
          (by simpa using d)⟩
  | rightOr p q hp hq _ ih =>
      intro R hR
      obtain ⟨d⟩ := ih R hR
      exact ⟨by
        simpa [R.formula_or hR hp hq] using Pure.ProofTree.rightOr (R.formula p) (R.formula q)
          (by simpa using d)⟩
  | rightImp p q hp hq _ ih =>
      intro R hR
      obtain ⟨d⟩ := ih R hR
      exact ⟨by
        simpa [R.formula_imp hR hp hq] using Pure.ProofTree.rightImp (R.formula p) (R.formula q)
          (by simpa using d)⟩
  | leftIff p q hp hq _ ih =>
      intro R hR
      obtain ⟨d⟩ := ih R hR
      exact ⟨by
        simpa [R.formula_iff hR hp hq] using
          Pure.ProofTree.leftIff (R.formula p) (R.formula q)
            (by simpa [R.formula_imp hR hp hq, R.formula_imp hR hq hp] using d)⟩
  | leftNot p hp _ ih =>
      intro R hR
      obtain ⟨d⟩ := ih R hR
      exact ⟨by simpa [R.formula_neg hR hp] using Pure.ProofTree.leftNot (R.formula p) (by simpa using d)⟩
  | rightNot p hp _ ih =>
      intro R hR
      obtain ⟨d⟩ := ih R hR
      exact ⟨by simpa [R.formula_neg hR hp] using Pure.ProofTree.rightNot (R.formula p) (by simpa using d)⟩
  | rightAnd p q hp hq _ _ ih₁ ih₂ =>
      intro R hR
      obtain ⟨d₁⟩ := ih₁ R hR
      obtain ⟨d₂⟩ := ih₂ R hR
      exact ⟨by
        simpa [R.formula_and hR hp hq] using Pure.ProofTree.rightAnd (R.formula p) (R.formula q)
          (by simpa using d₁) (by simpa using d₂)⟩
  | leftOr p q hp hq _ _ ih₁ ih₂ =>
      intro R hR
      obtain ⟨d₁⟩ := ih₁ R hR
      obtain ⟨d₂⟩ := ih₂ R hR
      exact ⟨by
        simpa [R.formula_or hR hp hq] using Pure.ProofTree.leftOr (R.formula p) (R.formula q)
          (by simpa using d₁) (by simpa using d₂)⟩
  | leftImp p q hp hq _ _ ih₁ ih₂ =>
      intro R hR
      obtain ⟨d₁⟩ := ih₁ R hR
      obtain ⟨d₂⟩ := ih₂ R hR
      exact ⟨by
        simpa [R.formula_imp hR hp hq] using Pure.ProofTree.leftImp (R.formula p) (R.formula q)
          (by simpa using d₁) (by simpa using d₂)⟩
  | rightIff p q hp hq _ _ ih₁ ih₂ =>
      intro R hR
      obtain ⟨d₁⟩ := ih₁ R hR
      obtain ⟨d₂⟩ := ih₂ R hR
      exact ⟨by
        simpa [R.formula_iff hR hp hq] using
          Pure.ProofTree.rightIff (R.formula p) (R.formula q)
            (by simpa [R.formula_imp hR hp hq, R.formula_imp hR hq hp] using d₁)
            (by simpa [R.formula_imp hR hp hq, R.formula_imp hR hq hp] using d₂)⟩
  | @leftForall Γ Δ x p t hx hp ht _ ih =>
      intro R hR
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, _, _⟩ := fresh_for_binders f f (R.classContext Γ) (R.classContext Δ)
      obtain ⟨d⟩ := ih R hR
      simp [R.formula_substOne x hp ht] at d
      rw [(R.predicate x p hp).read_apply y hy (R.expression t ht)] at d
      refine ⟨?_⟩
      simpa [R.formula_forall hR x hp, (R.predicate x p hp).read_all y hy]
        using Pure.ProofTree.leftForall y
          (f.app (ScopedExpr.individual y)).readFormula (R.expression t ht).readTerm d
  | @rightExists Γ Δ x p t hx hp ht _ ih =>
      intro R hR
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, _, _⟩ := fresh_for_binders f f (R.classContext Γ) (R.classContext Δ)
      obtain ⟨d⟩ := ih R hR
      simp [R.formula_substOne x hp ht] at d
      rw [(R.predicate x p hp).read_apply y hy (R.expression t ht)] at d
      refine ⟨?_⟩
      simpa [R.formula_exists hR x hp, (R.predicate x p hp).read_ex y hy]
        using Pure.ProofTree.rightExists y
          (f.app (ScopedExpr.individual y)).readFormula (R.expression t ht).readTerm d
  | @rightForall Γ Δ x p hx hp _ hxΓ hxΔ ih =>
      intro R hR
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, hyΓ, hyΔ⟩ := fresh_for_binders f f (R.classContext Γ) (R.classContext Δ)
      obtain ⟨d⟩ := ih (R.update ⟨x, ind⟩ (ScopedExpr.individual y)) (hR.update _ _)
      simp only [Assignment.classContext_insert, Assignment.formulaClass_ofExpr, 
        R.classContext_update_fresh _ _ Γ hxΓ,
        R.classContext_update_fresh _ _ Δ hxΔ, ← R.predicate_apply x hp] at d
      refine ⟨?_⟩
      simpa [R.formula_forall hR x hp, (R.predicate x p hp).read_all y hy]
        using Pure.ProofTree.rightForall y
          (f.app (ScopedExpr.individual y)).readFormula d hyΓ hyΔ
  | @leftExists Γ Δ x p hx hp _ hxΓ hxΔ ih =>
      intro R hR
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, hyΓ, hyΔ⟩ := fresh_for_binders f f (R.classContext Γ) (R.classContext Δ)
      obtain ⟨d⟩ := ih (R.update ⟨x, ind⟩ (ScopedExpr.individual y)) (hR.update _ _)
      simp only [Assignment.classContext_insert, Assignment.formulaClass_ofExpr, 
        R.classContext_update_fresh _ _ Γ hxΓ,
        R.classContext_update_fresh _ _ Δ hxΔ, ← R.predicate_apply x hp] at d
      refine ⟨?_⟩
      simpa [R.formula_exists hR x hp, (R.predicate x p hp).read_ex y hy]
        using Pure.ProofTree.leftExists y
          (f.app (ScopedExpr.individual y)).readFormula d hyΓ hyΔ
  | @rightEpsilon Γ Δ x p t hx hp ht _ ih =>
      intro R hR
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, _, _⟩ := fresh_for_binders f f (R.classContext Γ) (R.classContext Δ)
      obtain ⟨d⟩ := ih R hR
      simp [R.formula_substOne x hp ht] at d
      rw [(R.predicate x p hp).read_apply y hy (R.expression t ht)] at d
      refine ⟨?_⟩
      rw [Assignment.classContext_insert, Assignment.formulaClass_ofExpr,
        R.formula_substOne x hp (isTerm_epsilon (x := ⟨x, ind⟩) rfl hp),
        R.expression_epsilon hR x hp,
        (R.predicate x p hp).read_apply y hy (ScopedExpr.epsilon (R.predicate x p hp)),
        (R.predicate x p hp).read_epsilon y hy]
      exact Pure.ProofTree.epsilonWitness y
        (f.app (ScopedExpr.individual y)).readFormula (R.expression t ht).readTerm d
  | refl t ht =>
      intro R hR
      refine ⟨?_⟩
      simpa [R.formula_eq hR (p := t) (q := t) ht ht]
        using Pure.ProofTree.refl (R.expression t ht).readTerm
  | @leftReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂
  | @rightReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂ =>
      intro R hR
      obtain ⟨d₁⟩ := ih₁ R hR
      obtain ⟨de⟩ := substitution_rule_equiv_contexts R hR r hr (fun S => S.classContext Θ) (fun S => S.classContext Ξ)
        (fun c hc S he hs => ⟨R.classContext_agreeOutside S c.2 Θ he hs (fun x hx => (hf c hc x hx).1),
          R.classContext_agreeOutside S c.2 Ξ he hs (fun x hx => (hf c hc x hx).2)⟩)
        (fun S hS => by simpa only [Assignment.classContext_insert, Assignment.formulaClass_ofExpr] using ih₂ S hS)
      simp only [Assignment.classContext_insert, Assignment.formulaClass_ofExpr] at d₁
      refine ⟨?_⟩
      first
      | simpa only [Assignment.classContext_insert, Assignment.formulaClass_ofExpr, Assignment.classContext_union, Finset.insert_union, Finset.union_insert,
          Finset.union_comm] using Pure.ProofTree.cut (R.formula r.source) de.iff_backward d₁
      | simpa only [Assignment.classContext_insert, Assignment.formulaClass_ofExpr, Assignment.classContext_union, Finset.union_insert]
          using Pure.ProofTree.cut (R.formula r.source) d₁ de.iff_forward

end Lisa.SCLambdaToPure.A
