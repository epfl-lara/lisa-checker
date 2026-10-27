import Lisa.SCLambdaToPure.AToPure.RelatedExpressions
import Lisa.SCLambdaToPure.AToPure.ReadbackSubstitution
import Lisa.SCLambdaToPure.AToPure.FirstOrderReplacement

/-! Reading individual abstraction preserves the first-order binders.
Epsilon and quantifiers share the same abstraction calculation. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda
namespace ScopedExpr

def lambda (x : Identifier) (p : ScopedExpr prop) : ScopedExpr (ind >> prop) where
  term := .lam ind ((Replacement.abstract ⟨x, ind⟩).apply p.term)
  language := .lam (p.language.abstract x)
  subst_eq := Replacement.abstract_closed p.term p.subst_eq ⟨x, ind⟩

def all (f : ScopedExpr (ind >> prop)) : ScopedExpr prop := (constant _ .all).app f
def ex (f : ScopedExpr (ind >> prop)) : ScopedExpr prop := (constant _ .ex).app f
def epsilon (f : ScopedExpr (ind >> prop)) : ScopedExpr ind := (constant _ .epsilon).app f

theorem lambda_apply {x : Identifier} (f : ScopedExpr (ind >> prop))
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    Equiv (lambda x (f.app (individual x))).term f.term :=
  Replacement.abstract_eta (x := ⟨x, ind⟩) f.term hx

private theorem normalize_all_lambda (x : Identifier) (p : ScopedExpr prop) :
    normalize (all (lambda x p)).term = .app (.const ⟨"forall", 0⟩)
      (.lam ind ((Replacement.abstract ⟨x, ind⟩).apply (normalize p.term))) := by
  dsimp only [all, lambda, app, constant]
  rw [normalize_eq_of_equiv (Lambda.Equiv.app (.refl _) (.lam
    ((Replacement.abstract ⟨x, ind⟩).equiv (normalize_sound p.term))))]
  exact FirstOrderShape.normalize_formula_eq (.all
    ((FirstOrderShape.normalize_formula p.language p.subst_eq).replace (FirstOrderShape.preserves_abstract x)))

private theorem normalize_ex_lambda (x : Identifier) (p : ScopedExpr prop) :
    normalize (ex (lambda x p)).term = .app (.const ⟨"exists", 0⟩)
      (.lam ind ((Replacement.abstract ⟨x, ind⟩).apply (normalize p.term))) := by
  dsimp only [ex, lambda, app, constant]
  rw [normalize_eq_of_equiv (Lambda.Equiv.app (.refl _) (.lam
    ((Replacement.abstract ⟨x, ind⟩).equiv (normalize_sound p.term))))]
  exact FirstOrderShape.normalize_formula_eq (.ex
    ((FirstOrderShape.normalize_formula p.language p.subst_eq).replace (FirstOrderShape.preserves_abstract x)))

private theorem normalize_epsilon_lambda (x : Identifier) (p : ScopedExpr prop) :
    normalize (epsilon (lambda x p)).term = .app (.const ⟨"epsilon", 0⟩)
      (.lam ind ((Replacement.abstract ⟨x, ind⟩).apply (normalize p.term))) := by
  dsimp only [epsilon, lambda, app, constant]
  rw [normalize_eq_of_equiv (Lambda.Equiv.app (.refl _) (.lam
    ((Replacement.abstract ⟨x, ind⟩).equiv (normalize_sound p.term))))]
  exact FirstOrderShape.normalize_individual_eq (.epsilon
    ((FirstOrderShape.normalize_formula p.language p.subst_eq).replace (FirstOrderShape.preserves_abstract x)))

@[simp] theorem read_all_lambda (x : Identifier) (p : ScopedExpr prop) :
    (all (lambda x p)).readFormula = Pure.forall_ x p.readFormula := by
  have h := (all (lambda x p)).readFormula_spec
  rw [normalize_all_lambda] at h
  simp only [Readback.formula, Readback.formula_abstract p.readFormula_spec x] at h
  exact (Option.some.inj h).symm

@[simp] theorem read_ex_lambda (x : Identifier) (p : ScopedExpr prop) :
    (ex (lambda x p)).readFormula = Pure.exists_ x p.readFormula := by
  have h := (ex (lambda x p)).readFormula_spec
  rw [normalize_ex_lambda] at h
  simp only [Readback.formula, Readback.formula_abstract p.readFormula_spec x] at h
  exact (Option.some.inj h).symm

@[simp] theorem read_epsilon_lambda (x : Identifier) (p : ScopedExpr prop) :
    (epsilon (lambda x p)).readTerm = Pure.epsilon_ x p.readFormula := by
  have h := (epsilon (lambda x p)).readTerm_spec
  rw [normalize_epsilon_lambda] at h
  simp only [Readback.term, Readback.formula_abstract p.readFormula_spec x] at h
  exact (Option.some.inj h).symm

end ScopedExpr

theorem fresh_for_binders (f g : ScopedExpr (ind >> prop))
    (Γ Δ : Pure.Context Readback.language) :
    ∃ x : Identifier, SVar.mk x ind ∉ f.term.freeVars ∧ SVar.mk x ind ∉ g.term.freeVars ∧
      Pure.Fresh x Γ ∧ Pure.Fresh x Δ := by
  let blocked := (f.term.freeVars ∪ g.term.freeVars).image (fun v => v.id) ∪
    (Γ ∪ Δ).biUnion Pure.BFormula.freeVars
  let x := freshId blocked ⟨"_eigen", 0⟩
  have hx : x ∉ blocked := freshId_not_mem _ _
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hx (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨⟨x, ind⟩, Finset.mem_union_left _ h, rfl⟩))
  · intro h
    exact hx (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨⟨x, ind⟩, Finset.mem_union_right _ h, rfl⟩))
  · intro p hp h
    exact hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_union_left _ hp, h⟩))
  · intro p hp h
    exact hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_union_right _ hp, h⟩))

theorem related_all : Related Γ Δ ((ind >> prop) >> prop)
    (ScopedExpr.constant _ .all) (ScopedExpr.constant _ .all) := by
  intro f g h
  obtain ⟨x, hxf, hxg, hΓ, hΔ⟩ := fresh_for_binders f g Γ Δ
  obtain ⟨d⟩ := h (ScopedExpr.individual x) (ScopedExpr.individual x) ⟨.reflexive _⟩
  -- Apply the first-order rule to the bodies, then use eta to recover f and g.
  have step : Related Γ Δ prop
      (ScopedExpr.all (ScopedExpr.lambda x (f.app (ScopedExpr.individual x))))
      (ScopedExpr.all (ScopedExpr.lambda x (g.app (ScopedExpr.individual x)))) := by
    simpa [Related] using (show Pure.Provable Γ _ from ⟨d.forall_congr x hΓ hΔ⟩)
  exact step.convert (.app (.refl _) (ScopedExpr.lambda_apply f hxf))
    (.app (.refl _) (ScopedExpr.lambda_apply g hxg))

theorem related_ex : Related Γ Δ ((ind >> prop) >> prop)
    (ScopedExpr.constant _ .ex) (ScopedExpr.constant _ .ex) := by
  intro f g h
  obtain ⟨x, hxf, hxg, hΓ, hΔ⟩ := fresh_for_binders f g Γ Δ
  obtain ⟨d⟩ := h (ScopedExpr.individual x) (ScopedExpr.individual x) ⟨.reflexive _⟩
  -- Apply the first-order rule to the bodies, then use eta to recover f and g.
  have step : Related Γ Δ prop
      (ScopedExpr.ex (ScopedExpr.lambda x (f.app (ScopedExpr.individual x))))
      (ScopedExpr.ex (ScopedExpr.lambda x (g.app (ScopedExpr.individual x)))) := by
    simpa [Related] using (show Pure.Provable Γ _ from ⟨d.exists_congr x hΓ hΔ⟩)
  exact step.convert (.app (.refl _) (ScopedExpr.lambda_apply f hxf))
    (.app (.refl _) (ScopedExpr.lambda_apply g hxg))

theorem related_epsilon : Related Γ Δ ((ind >> prop) >> ind)
    (ScopedExpr.constant _ .epsilon) (ScopedExpr.constant _ .epsilon) := by
  intro f g h
  obtain ⟨x, hxf, hxg, hΓ, hΔ⟩ := fresh_for_binders f g Γ Δ
  obtain ⟨d⟩ := h (ScopedExpr.individual x) (ScopedExpr.individual x) ⟨.reflexive _⟩
  -- Apply the first-order rule to the bodies, then use eta to recover f and g.
  have step : Related Γ Δ ind
      (ScopedExpr.epsilon (ScopedExpr.lambda x (f.app (ScopedExpr.individual x))))
      (ScopedExpr.epsilon (ScopedExpr.lambda x (g.app (ScopedExpr.individual x)))) := by
    simpa [Related] using (show Pure.Provable Γ _ from ⟨Pure.ProofTree.epsilonExt x _ _ d hΓ hΔ⟩)
  exact step.convert (.app (.refl _) (ScopedExpr.lambda_apply f hxf))
    (.app (.refl _) (ScopedExpr.lambda_apply g hxg))

end Lisa.SCLambdaToPure.Syntactic
