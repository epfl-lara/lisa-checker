import Lisa.LambdaFol.ToPureFol.ScopedSubstitution
import Lisa.LambdaFol.ToPureFol.PureFolTranslationSubstitution
import Lisa.LambdaFol.ToPureFol.FirstOrderSubstitution

/-! Translate individual binders and predicate applications to PureFol.
Quantifiers and epsilon share the abstraction calculation. Applying a predicate
is translated as substitution in its body, expressed using a fresh name. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization.Algorithm
namespace FirstOrderCompatibleExpr

def lambda (x : Identifier) (p : FirstOrderCompatibleExpr prop) : FirstOrderCompatibleExpr (ind >> prop) where
  term := .lam ind ((SymbolSubstitution.abstract ⟨x, ind⟩).apply p.term)
  language := .lam (p.language.abstract x)
  subst_eq := SymbolSubstitution.abstract_locallyClosed p.term p.subst_eq ⟨x, ind⟩

def all (f : FirstOrderCompatibleExpr (ind >> prop)) : FirstOrderCompatibleExpr prop := (constant _ .all).app f
def ex (f : FirstOrderCompatibleExpr (ind >> prop)) : FirstOrderCompatibleExpr prop := (constant _ .ex).app f
def epsilon (f : FirstOrderCompatibleExpr (ind >> prop)) : FirstOrderCompatibleExpr ind := (constant _ .epsilon).app f

theorem eta {x : Identifier} (f : FirstOrderCompatibleExpr (ind >> prop))
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    Equiv (lambda x (f.app (individual x))).term f.term :=
  SymbolSubstitution.abstract_eta (x := ⟨x, ind⟩) f.term hx

/-- Normalize the body of an individual abstraction once; all three binders
then use the same result. The first-order shape theorem supplies the fixed point. -/
private theorem normalize_lambda (x : Identifier) (p : FirstOrderCompatibleExpr prop) :
    normalize (lambda x p).term =
      .lam ind ((SymbolSubstitution.abstract ⟨x, ind⟩).apply (normalize p.term)) := by
  have h : normalize (all (lambda x p)).term = .app (.const ⟨"forall", 0⟩)
      (.lam ind ((SymbolSubstitution.abstract ⟨x, ind⟩).apply (normalize p.term))) := by
    dsimp only [all, lambda, app, constant]
    rw [normalize_eq_of_equiv (AlphaBetaEtaNormalization.Algorithm.Equiv.app (.refl _) (.lam
      ((SymbolSubstitution.abstract ⟨x, ind⟩).equiv (normalize_sound p.term))))]
    exact FirstOrderShape.normalize_formula_eq (.all
      ((FirstOrderShape.normalize_formula p.language p.subst_eq).replace
        (FirstOrderShape.preserves_abstract x)))
  change Term.app (Term.const ⟨"forall", 0⟩) (normalize (lambda x p).term) = _ at h
  simpa only [Term.app.injEq, heq_eq_eq, true_and] using h

@[simp] theorem toPureFolFormula_all_lambda (x : Identifier) (p : FirstOrderCompatibleExpr prop) :
    (all (lambda x p)).toPureFolFormula = PureFol.forall_ x p.toPureFolFormula := by
  have h := (all (lambda x p)).toPureFolFormula_spec
  change PureFolTranslation.fromNormalFormula? (fun _ => none)
    (.app (.const ⟨"forall", 0⟩) (normalize (lambda x p).term)) = _ at h
  rw [normalize_lambda] at h
  simp only [PureFolTranslation.fromNormalFormula?, PureFolTranslation.fromNormalFormula_abstract p.toPureFolFormula_spec x] at h
  exact (Option.some.inj h).symm

@[simp] theorem toPureFolFormula_ex_lambda (x : Identifier) (p : FirstOrderCompatibleExpr prop) :
    (ex (lambda x p)).toPureFolFormula = PureFol.exists_ x p.toPureFolFormula := by
  have h := (ex (lambda x p)).toPureFolFormula_spec
  change PureFolTranslation.fromNormalFormula? (fun _ => none)
    (.app (.const ⟨"exists", 0⟩) (normalize (lambda x p).term)) = _ at h
  rw [normalize_lambda] at h
  simp only [PureFolTranslation.fromNormalFormula?, PureFolTranslation.fromNormalFormula_abstract p.toPureFolFormula_spec x] at h
  exact (Option.some.inj h).symm

@[simp] theorem toPureFolTerm_epsilon_lambda (x : Identifier) (p : FirstOrderCompatibleExpr prop) :
    (epsilon (lambda x p)).toPureFolTerm = PureFol.epsilon_ x p.toPureFolFormula := by
  have h := (epsilon (lambda x p)).toPureFolTerm_spec
  change PureFolTranslation.fromNormalTerm? (fun _ => none)
    (.app (.const ⟨"epsilon", 0⟩) (normalize (lambda x p).term)) = _ at h
  rw [normalize_lambda] at h
  simp only [PureFolTranslation.fromNormalTerm?, PureFolTranslation.fromNormalFormula_abstract p.toPureFolFormula_spec x] at h
  exact (Option.some.inj h).symm

/-- Fresh individual names let us express application as substitution in PureFol. -/
theorem toPureFolFormula_apply (f : FirstOrderCompatibleExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) (a : FirstOrderCompatibleExpr ind) :
    (f.app a).toPureFolFormula = PureFol.substOne x a.toPureFolTerm
      (f.app (individual x)).toPureFolFormula := by
  have h : (f.app (individual x)).substIndividual x a = f.app a := by
    apply FirstOrderCompatibleExpr.ext
    change Term.app ((SymbolSubstitution.single ⟨x, ind⟩ a.term).apply f.term)
      ((SymbolSubstitution.single ⟨x, ind⟩ a.term).apply (.free x)) = _
    rw [SymbolSubstitution.single_fresh f.term ⟨x, ind⟩ a.term hx]
    simp [SymbolSubstitution.apply, SymbolSubstitution.single, app]
  rw [← h, toPureFolFormula_subst]

theorem toPureFolFormula_all (f : FirstOrderCompatibleExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    (all f).toPureFolFormula = PureFol.forall_ x (f.app (individual x)).toPureFolFormula := by
  rw [← toPureFolFormula_all_lambda x (f.app (individual x))]
  exact toPureFolFormula_equiv (e := all f) (f := all (lambda x (f.app (individual x))))
    (by exact .app (.refl _) (eta f hx).symm)

theorem toPureFolFormula_ex (f : FirstOrderCompatibleExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    (ex f).toPureFolFormula = PureFol.exists_ x (f.app (individual x)).toPureFolFormula := by
  rw [← toPureFolFormula_ex_lambda x (f.app (individual x))]
  exact toPureFolFormula_equiv (e := ex f) (f := ex (lambda x (f.app (individual x))))
    (by exact .app (.refl _) (eta f hx).symm)

theorem toPureFolTerm_epsilon (f : FirstOrderCompatibleExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    (epsilon f).toPureFolTerm = PureFol.epsilon_ x (f.app (individual x)).toPureFolFormula := by
  rw [← toPureFolTerm_epsilon_lambda x (f.app (individual x))]
  exact toPureFolTerm_equiv (e := epsilon f) (f := epsilon (lambda x (f.app (individual x))))
    (by exact .app (.refl _) (eta f hx).symm)

end FirstOrderCompatibleExpr

/-- Choose an individual name fresh for the predicates and both formula sets. -/
noncomputable def freshForBinders (f g : FirstOrderCompatibleExpr (ind >> prop))
    (Γ Δ : Finset (PureFol.Formula PureFolTranslation.language)) :
    {x : Identifier // SVar.mk x ind ∉ f.term.freeVars ∧ SVar.mk x ind ∉ g.term.freeVars ∧
      PureFol.Fresh x Γ ∧ PureFol.Fresh x Δ} := by
  let blocked := (f.term.freeVars ∪ g.term.freeVars).image (fun v => v.id) ∪
    (Γ ∪ Δ).biUnion PureFol.BoundedFormula.freeVars
  let x := freshId blocked ⟨"_eigen", 0⟩
  have hx : x ∉ blocked := freshId_not_mem _ _
  have hf : SVar.mk x ind ∉ f.term.freeVars ∪ g.term.freeVars :=
    fun h => hx (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨x, ind⟩, h, rfl⟩))
  have hΓΔ : PureFol.Fresh x (Γ ∪ Δ) :=
    fun p hp h => hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, h⟩))
  refine ⟨x, ?_⟩
  simpa [PureFol.Fresh, or_imp, forall_and, and_assoc] using And.intro hf hΓΔ

end Lisa.LambdaFol
