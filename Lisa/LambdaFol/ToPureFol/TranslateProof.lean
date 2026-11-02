import Lisa.LambdaFol.WithoutInstantiation
import Lisa.LambdaFol.ToPureFol.FormulaClasses
import Lisa.LambdaFol.ToPureFol.ReplacementRule
import Lisa.LambdaFol.ToPureFol.TranslateNamedExpressions

/-! System WithoutInstantiation translates by default assignment, normalization, and translation to PureFol.
There is no schematic-instantiation case: LambdaFol → WithoutInstantiation has already removed those nodes.
All intermediate formulas remain unrestricted.

The induction works for any assignment fixing the admitted constants. In the
eigenvariable cases it changes the assignment to a fresh target variable;
in the replacement cases it uses `replacement_preserves_provable_iff`.
`WithoutInstantiation.Provable.toPureFol` later selects the default assignment and recovers the original conclusion. -/
namespace Lisa.LambdaFol.WithoutInstantiation


/-- Translate WithoutInstantiation under any assignment of schematic symbols to sorted expressions
of the first-order epsilon fragment. This is a syntactic assignment, not a model. -/
noncomputable def ProofTree.toPureFol {Γ Δ : Finset LambdaFol.Formula} (d : WithoutInstantiation.ProofTree Γ Δ)
    (R : FirstOrderAssignment) (hR : R.FixesConstants) :
    PureFol.ProofTree (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ) := by
  induction d generalizing R with
  | weakening _ hΓ hΔ ih =>
      exact (ih R hR).weakening (Finset.image_mono R.toPureFolFormulaClass hΓ) (Finset.image_mono R.toPureFolFormulaClass hΔ)
  | rightTrue =>
      simpa [R.toPureFolFormula_top hR] using (PureFol.ProofTree.rightTrue (L := PureFolTranslation.language))
  | leftFalse =>
      simpa [R.toPureFolFormula_bot hR] using (PureFol.ProofTree.leftFalse (L := PureFolTranslation.language))
  | hypothesis p =>
      simpa using PureFol.ProofTree.hypothesis (R.toPureFolFormulaClass p)
  | cut p _ _ ih₁ ih₂ =>
      simpa using PureFol.ProofTree.cut (R.toPureFolFormulaClass p)
        (by simpa using ih₁ R hR) (by simpa using ih₂ R hR)
  | leftAnd p q hp hq _ ih =>
      simpa [R.toPureFolFormula_and hR hp hq] using PureFol.ProofTree.leftAnd (R.toPureFolFormula p) (R.toPureFolFormula q)
        (by simpa using ih R hR)
  | rightOr p q hp hq _ ih =>
      simpa [R.toPureFolFormula_or hR hp hq] using PureFol.ProofTree.rightOr (R.toPureFolFormula p) (R.toPureFolFormula q)
        (by simpa using ih R hR)
  | rightImp p q hp hq _ ih =>
      simpa [R.toPureFolFormula_imp hR hp hq] using PureFol.ProofTree.rightImp (R.toPureFolFormula p) (R.toPureFolFormula q)
        (by simpa using ih R hR)
  | leftIff p q hp hq _ ih =>
      simpa [R.toPureFolFormula_iff hR hp hq] using
        PureFol.ProofTree.leftIff (R.toPureFolFormula p) (R.toPureFolFormula q)
          (by simpa [R.toPureFolFormula_imp hR hp hq, R.toPureFolFormula_imp hR hq hp] using ih R hR)
  | leftNot p hp _ ih =>
      simpa [R.toPureFolFormula_neg hR hp] using PureFol.ProofTree.leftNot (R.toPureFolFormula p) (by simpa using ih R hR)
  | rightNot p hp _ ih =>
      simpa [R.toPureFolFormula_neg hR hp] using PureFol.ProofTree.rightNot (R.toPureFolFormula p) (by simpa using ih R hR)
  | rightAnd p q hp hq _ _ ih₁ ih₂ =>
      simpa [R.toPureFolFormula_and hR hp hq] using PureFol.ProofTree.rightAnd (R.toPureFolFormula p) (R.toPureFolFormula q)
        (by simpa using ih₁ R hR) (by simpa using ih₂ R hR)
  | leftOr p q hp hq _ _ ih₁ ih₂ =>
      simpa [R.toPureFolFormula_or hR hp hq] using PureFol.ProofTree.leftOr (R.toPureFolFormula p) (R.toPureFolFormula q)
        (by simpa using ih₁ R hR) (by simpa using ih₂ R hR)
  | leftImp p q hp hq _ _ ih₁ ih₂ =>
      simpa [R.toPureFolFormula_imp hR hp hq] using PureFol.ProofTree.leftImp (R.toPureFolFormula p) (R.toPureFolFormula q)
        (by simpa using ih₁ R hR) (by simpa using ih₂ R hR)
  | rightIff p q hp hq _ _ ih₁ ih₂ =>
      simpa [R.toPureFolFormula_iff hR hp hq] using
        PureFol.ProofTree.rightIff (R.toPureFolFormula p) (R.toPureFolFormula q)
          (by simpa [R.toPureFolFormula_imp hR hp hq, R.toPureFolFormula_imp hR hq hp] using ih₁ R hR)
          (by simpa [R.toPureFolFormula_imp hR hp hq, R.toPureFolFormula_imp hR hq hp] using ih₂ R hR)
  | @leftForall Γ Δ x p t hx hp ht _ ih =>
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, _, _⟩ := freshForBinders f f (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ)
      simpa [R.toPureFolFormula_forall hR x hp y hy] using
        PureFol.ProofTree.leftForall y
          ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) (R.applyExpr t ht).toPureFolTerm
          (by simpa [R.toPureFolFormula_substOne x hp ht y hy] using ih R hR)
  | @rightExists Γ Δ x p t hx hp ht _ ih =>
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, _, _⟩ := freshForBinders f f (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ)
      simpa [R.toPureFolFormula_exists hR x hp y hy] using
        PureFol.ProofTree.rightExists y
          ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) (R.applyExpr t ht).toPureFolTerm
          (by simpa [R.toPureFolFormula_substOne x hp ht y hy] using ih R hR)
  | @rightForall Γ Δ x p hx hp _ hxΓ hxΔ ih =>
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, hyΓ, hyΔ⟩ := freshForBinders f f (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ)
      have d := ih (R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)) (hR.update _ _)
      simp only [FirstOrderAssignment.toPureFolFormulaClassSet_insert, FirstOrderAssignment.toPureFolFormulaClass_ofExpr,
        R.toPureFolFormulaClassSet_update_fresh _ _ Γ hxΓ,
        R.toPureFolFormulaClassSet_update_fresh _ _ Δ hxΔ] at d
      simpa [R.toPureFolFormula_forall hR x hp y hy]
        using PureFol.ProofTree.rightForall y
          ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) d hyΓ hyΔ
  | @leftExists Γ Δ x p hx hp _ hxΓ hxΔ ih =>
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, hyΓ, hyΔ⟩ := freshForBinders f f (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ)
      have d := ih (R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)) (hR.update _ _)
      simp only [FirstOrderAssignment.toPureFolFormulaClassSet_insert, FirstOrderAssignment.toPureFolFormulaClass_ofExpr,
        R.toPureFolFormulaClassSet_update_fresh _ _ Γ hxΓ,
        R.toPureFolFormulaClassSet_update_fresh _ _ Δ hxΔ] at d
      simpa [R.toPureFolFormula_exists hR x hp y hy]
        using PureFol.ProofTree.leftExists y
          ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) d hyΓ hyΔ
  | @rightEpsilon Γ Δ x p t hx hp ht _ ih =>
      rcases x with ⟨x, s⟩
      change s = ind at hx
      subst s
      let f := R.predicate x p hp
      obtain ⟨y, hy, _, _, _⟩ := freshForBinders f f (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ)
      simpa [R.toPureFolFormula_substOne x hp (isTerm_epsilon (x := ⟨x, ind⟩) rfl hp) y hy,
        R.term_epsilon hR x hp y hy] using
        PureFol.ProofTree.epsilonWitness y
          ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) (R.applyExpr t ht).toPureFolTerm
          (by simpa [R.toPureFolFormula_substOne x hp ht y hy] using ih R hR)
  | refl t ht =>
      simpa [R.toPureFolFormula_eq hR (p := t) (q := t) ht ht]
        using PureFol.ProofTree.refl (R.applyExpr t ht).toPureFolTerm
  | @leftReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂
  | @rightReplace Γ Δ Θ Ξ r hr hf _ _ ih₁ ih₂ =>
      have d₁ := ih₁ R hR
      let de := Classical.choice (replacement_preserves_provable_iff R hR r hr (fun S => S.toPureFolFormulaClassSet Θ) (fun S => S.toPureFolFormulaClassSet Ξ)
        (fun c hc S he hs => ⟨R.toPureFolFormulaClassSet_agreeOutside S c.2 Θ he hs (fun x hx => (hf c hc x hx).1),
          R.toPureFolFormulaClassSet_agreeOutside S c.2 Ξ he hs (fun x hx => (hf c hc x hx).2)⟩)
        (fun S hS => by simpa only [FirstOrderAssignment.toPureFolFormulaClassSet_insert, FirstOrderAssignment.toPureFolFormulaClass_ofExpr] using (show PureFol.Provable _ _ from ⟨ih₂ S hS⟩)))
      simp only [FirstOrderAssignment.toPureFolFormulaClassSet_insert, FirstOrderAssignment.toPureFolFormulaClass_ofExpr] at d₁
      first
      | simpa only [FirstOrderAssignment.toPureFolFormulaClassSet_insert, FirstOrderAssignment.toPureFolFormulaClass_ofExpr, FirstOrderAssignment.toPureFolFormulaClassSet_union, Finset.insert_union, Finset.union_insert,
          Finset.union_comm] using PureFol.ProofTree.cut (R.toPureFolFormula r.source) de.iff_backward d₁
      | simpa only [FirstOrderAssignment.toPureFolFormulaClassSet_insert, FirstOrderAssignment.toPureFolFormulaClass_ofExpr, FirstOrderAssignment.toPureFolFormulaClassSet_union, Finset.union_insert]
          using PureFol.ProofTree.cut (R.toPureFolFormula r.source) d₁ de.iff_forward

/-- Provability follows by constructing the translated proof. -/
theorem ProofTree.provable_toPureFol {Γ Δ : Finset LambdaFol.Formula} (d : WithoutInstantiation.ProofTree Γ Δ) :
    ∀ R : FirstOrderAssignment, R.FixesConstants →
      PureFol.Provable (R.toPureFolFormulaClassSet Γ) (R.toPureFolFormulaClassSet Δ) :=
  fun R hR => ⟨ProofTree.toPureFol d R hR⟩

end Lisa.LambdaFol.WithoutInstantiation
