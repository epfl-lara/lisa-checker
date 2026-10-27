import Lisa.SCLambdaToPure.AToPure.ScopedSubstitution
import Lisa.SCLambdaToPure.AToPure.Binders

/-! Ground higher-order symbols using default expressions while fixing first-order
and logical constants. This assignment preserves the syntactic relation and is
the identity on scoped expressions already in the first-order language. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda

theorem related_constant (h : FirstOrderShape.Constant s c) :
    Related Γ Δ s (ScopedExpr.constant c h) (ScopedExpr.constant c h) := by
  cases h with
  | function n c => exact related_firstOrder_refl (Or.inl rfl) _
  | predicate n c => exact related_firstOrder_refl (Or.inr rfl) _
  | top | bot => exact related_ground_refl (Or.inr rfl) _
  | neg => exact related_neg
  | and => exact related_and
  | or => exact related_or
  | imp => exact related_imp
  | iff => exact related_iff
  | eq => exact related_equal
  | all => exact related_all
  | ex => exact related_ex
  | epsilon => exact related_epsilon

namespace ScopedExpr

def constantFunction (b : LSort) (e : ScopedExpr s) : ScopedExpr (b >> s) where
  term := .lam b (e.term.shift b)
  language := .lam (e.language.rename _)
  subst_eq σ := by
    apply congrArg (Term.lam b)
    rw [Term.subst_rename]
    change (e.term.subst (fun u n => (σ.lift b) u ((Ren.shift b) u n))) = _
    rw [e.subst_eq]
    change e.term = e.term.rename (Ren.shift b)
    rw [← Term.subst_ofRen, e.subst_eq]

theorem constantFunction_apply (b : LSort) (e : ScopedExpr s) (a : ScopedExpr b) :
    Equiv ((constantFunction b e).app a).term e.term := by
  simpa only [constantFunction, app, Term.shift_instantiate] using
    (Lambda.Equiv.beta (e.term.shift b) a.term)

/-- A closed expression of every simple sort, using epsilon for the individual
case rather than extending the signature with a new constant. -/
def default : (s : LSort) → ScopedExpr s
  | .ind => epsilon (constantFunction ind (constant _ .top))
  | .prop => constant _ .top
  | .arrow s t => constantFunction s (default t)

end ScopedExpr

theorem related_default (s : LSort) : Related Γ Δ s (ScopedExpr.default s) (ScopedExpr.default s) := by
  induction s with
  | ind => exact related_ground_refl (Or.inl rfl) _
  | prop => exact related_ground_refl (Or.inr rfl) _
  | arrow s t _ ih =>
      intro a b _
      exact Related.convert (ScopedExpr.constantFunction_apply s _ a).symm
        (ScopedExpr.constantFunction_apply s _ b).symm ih

/-! Grounding is the identity on complete expressions in the chosen boundary.
All such expressions preserve the relation defined by first-order derivations,
including at higher simple sorts. -/

namespace Assignment

noncomputable def grounding : Assignment where
  bound s _ := ScopedExpr.default s
  free s x := match s with
    | .ind => ScopedExpr.individual x
    | .prop => ScopedExpr.proposition x
    | .arrow a b => ScopedExpr.default (.arrow a b)
  const s c := by
    classical
    exact if h : FirstOrderShape.Constant s c then ScopedExpr.constant c h else ScopedExpr.default s

theorem grounding_related : RelatedAssignments Γ Δ grounding grounding where
  bound s _ := related_default s
  free := by
    intro s x; cases s with
    | ind => exact related_ground_refl (Or.inl rfl) _
    | prop => exact related_ground_refl (Or.inr rfl) _
    | arrow _ _ => exact related_default _
  const := by
    intro s c
    by_cases h : FirstOrderShape.Constant s c
    · simpa only [grounding, h, ↓reduceDIte] using related_constant (Γ := Γ) (Δ := Δ) h
    · simpa only [grounding, h, ↓reduceDIte] using related_default (Γ := Γ) (Δ := Δ) s

end Assignment

private theorem replace_fixed {e : Term s} (h : FirstOrderShape.InLanguage e) (R : Replacement)
    (hb : ∀ u n, R.bound u n = .bound n)
    (hi : ∀ x, R.free ind x = .free x) (hp : ∀ x, R.free prop x = .free x)
    (hc : ∀ u c, FirstOrderShape.Constant u c → R.const u c = .const c) : R.apply e = e := by
  induction h generalizing R with
  | bound n => exact hb _ n
  | individual x => exact hi x
  | proposition x => exact hp x
  | const h => exact hc _ _ h
  | app _ _ ihf iha => exact congrArg₂ Term.app (ihf R hb hi hp hc) (iha R hb hi hp hc)
  | @lam t b e he ih =>
      apply congrArg (Term.lam b)
      apply ih (R.lift b)
      · intro u n
        by_cases h : u = b
        · subst u; cases n <;> simp [Replacement.lift, hb, Term.rename, Ren.shift]
        · simp [Replacement.lift, hb, Term.rename, Ren.shift, h]
      · intro x; simp [Replacement.lift, hi, Term.rename]
      · intro x; simp [Replacement.lift, hp, Term.rename]
      · intro u c h; simp [Replacement.lift, hc u c h, Term.rename]

theorem Assignment.grounding_apply (e : ScopedExpr s) : grounding.apply e.term = e := by
  apply ScopedExpr.ext
  let R : Replacement := { grounding.replacement with bound := Sub.id }
  have h : grounding.replacement.apply e.term = R.apply e.term :=
    Replacement.apply_closed_congr e.term e.subst_eq _ _ rfl rfl
  change grounding.replacement.apply e.term = e.term
  rw [h]
  apply replace_fixed e.language R
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro u c hc
    simp [R, grounding, replacement, hc, ScopedExpr.constant]

/-- Every expression admitted by the boundary respects provable equality and
equivalence. Arrow sorts use related arguments, not higher-order equality in
the target language. -/
theorem related_refl (e : ScopedExpr s) : Related Γ Δ s e e := by
  simpa only [Assignment.grounding_apply] using
    fundamental e.term (Assignment.grounding_related (Γ := Γ) (Δ := Δ))

end Lisa.SCLambdaToPure.Syntactic
