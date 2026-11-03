import Lisa.LambdaFol.ToPureFol.Binders

/-! Replace higher-order symbols with default expressions while fixing first-order
and logical constants. The assignment is the identity on complete expressions
already using that signature and only free individual and proposition variables. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization

namespace FirstOrderCompatibleExpr

/-- A complete expression can be placed under an unused binder unchanged. -/
def constantFunction (b : LSort) (e : FirstOrderCompatibleExpr s) : FirstOrderCompatibleExpr (b >> s) where
  term := .lam b e.term
  language := .lam e.language
  subst_eq σ := congrArg (Term.lam b) (e.subst_eq (σ.lift b))

theorem constantFunction_apply (b : LSort) (e : FirstOrderCompatibleExpr s) (a : FirstOrderCompatibleExpr b) :
    Equiv ((constantFunction b e).app a).term e.term := by
  simpa only [constantFunction, app, Term.instantiate, e.subst_eq] using
    (AlphaBetaEtaNormalization.Equiv.beta e.term a.term)

/-- A closed expression of every simple sort: `εx. ⊤` at individual sort, `⊤`
at proposition sort, and constant functions at arrow sorts. -/
def default : (s : LSort) → FirstOrderCompatibleExpr s
  | .ind => epsilon (constantFunction ind (constant _ .top))
  | .prop => constant _ .top
  | .arrow s t => constantFunction s (default t)

end FirstOrderCompatibleExpr

/-! The default assignment is the identity on complete expressions satisfying the first-order restrictions.
The expressions can still contain higher-order lambda abstractions. -/

namespace FirstOrderAssignment

noncomputable def defaultAssignment : FirstOrderAssignment where
  bound s _ := FirstOrderCompatibleExpr.default s
  free s x := match s with
    | .ind => FirstOrderCompatibleExpr.individual x
    | .prop => FirstOrderCompatibleExpr.proposition x
    | .arrow a b => FirstOrderCompatibleExpr.default (.arrow a b)
  const s c := by
    classical
    exact if h : FirstOrderShape.AllowedConstant s c then FirstOrderCompatibleExpr.constant c h else FirstOrderCompatibleExpr.default s

theorem defaultAssignment_fixesConstants : defaultAssignment.FixesConstants := by
  intro s c h
  simp [defaultAssignment, h]

end FirstOrderAssignment

private theorem replace_fixed {e : Term s} (h : FirstOrderShape.Compatible e) (R : SymbolSubstitution)
    (hb : ∀ u n, R.bound u n = .bound n)
    (hi : ∀ x, R.free ind x = .free x) (hp : ∀ x, R.free prop x = .free x)
    (hc : ∀ u c, FirstOrderShape.AllowedConstant u c → R.const u c = .const c) : R.apply e = e := by
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
        · subst u; cases n <;> simp [SymbolSubstitution.lift, hb, Term.rename, Ren.shift]
        · simp [SymbolSubstitution.lift, hb, Term.rename, Ren.shift, h]
      · intro x; simp [SymbolSubstitution.lift, hi, Term.rename]
      · intro x; simp [SymbolSubstitution.lift, hp, Term.rename]
      · intro u c h; simp [SymbolSubstitution.lift, hc u c h, Term.rename]

theorem FirstOrderAssignment.defaultAssignment_apply (e : FirstOrderCompatibleExpr s) : defaultAssignment.apply e.term = e := by
  apply FirstOrderCompatibleExpr.ext
  let R : SymbolSubstitution := { defaultAssignment.replacement with bound := Sub.id }
  have h : defaultAssignment.replacement.apply e.term = R.apply e.term :=
    SymbolSubstitution.apply_locallyClosed_congr e.term e.subst_eq _ _ rfl rfl
  change defaultAssignment.replacement.apply e.term = e.term
  rw [h]
  apply replace_fixed e.language R
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro u c hc
    simp [R, defaultAssignment, replacement, hc, FirstOrderCompatibleExpr.constant]

end Lisa.LambdaFol
