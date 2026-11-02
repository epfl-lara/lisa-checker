import Lisa.LambdaFol.ToPureFol.PureFolTranslation

/-! Expressions and symbol assignments used by the translation.
`FirstOrderCompatibleExpr` wraps lambda syntax over the first-order signature, with
no dangling bound indices. `FirstOrderAssignment` replaces source leaves by such expressions.
The translation normalizes these expressions and writes the result in PureFol syntax. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization
open FirstOrderShape (Compatible)

/-- AlphaBetaEtaNormalization syntax over the first-order signature, before normalization, with no
dangling bound indices. Free individual and proposition names are allowed. -/
structure FirstOrderCompatibleExpr (s : LSort) where
  term : Term s
  language : Compatible term
  /-- Substitution of ambient bound indices has no effect. -/
  subst_eq : ∀ σ, term.subst σ = term

namespace FirstOrderCompatibleExpr
@[ext] theorem ext {e f : FirstOrderCompatibleExpr s} (h : e.term = f.term) : e = f := by
  cases e; cases f; cases h; rfl

def app (f : FirstOrderCompatibleExpr (s >> t)) (a : FirstOrderCompatibleExpr s) : FirstOrderCompatibleExpr t where
  term := .app f.term a.term
  language := .app f.language a.language
  subst_eq σ := congrArg₂ Term.app (f.subst_eq σ) (a.subst_eq σ)

def individual (x : Identifier) : FirstOrderCompatibleExpr ind := ⟨.free x, .individual x, by intros; rfl⟩
def proposition (x : Identifier) : FirstOrderCompatibleExpr prop := ⟨.free x, .proposition x, by intros; rfl⟩
def constant (c : Identifier) (h : FirstOrderShape.AllowedConstant s c) : FirstOrderCompatibleExpr s :=
  ⟨.const c, .const h, by intros; rfl⟩

def toPureFolTerm (e : FirstOrderCompatibleExpr ind) : PureFol.Term PureFolTranslation.language :=
  (PureFolTranslation.fromNormalTerm? (fun _ => none) (normalize e.term)).get
    (PureFolTranslation.fromNormalTerm_isSome (FirstOrderShape.normalize_individual e.language e.subst_eq)
      (normalize_scoped e.term e.subst_eq) _ (by simp [Depth.zero]))

def toPureFolFormula (e : FirstOrderCompatibleExpr prop) : PureFol.Formula PureFolTranslation.language :=
  (PureFolTranslation.fromNormalFormula? (fun _ => none) (normalize e.term)).get
    (PureFolTranslation.fromNormalFormula_isSome (FirstOrderShape.normalize_formula e.language e.subst_eq)
      (normalize_scoped e.term e.subst_eq) _ (by simp [Depth.zero]))

theorem toPureFolTerm_spec (e : FirstOrderCompatibleExpr ind) :
    PureFolTranslation.fromNormalTerm? (fun _ => none) (normalize e.term) = some e.toPureFolTerm := by
  simp [toPureFolTerm]

theorem toPureFolFormula_spec (e : FirstOrderCompatibleExpr prop) :
    PureFolTranslation.fromNormalFormula? (fun _ => none) (normalize e.term) = some e.toPureFolFormula := by
  simp [toPureFolFormula]

theorem toPureFolTerm_equiv {e f : FirstOrderCompatibleExpr ind} (h : Equiv e.term f.term) :
    e.toPureFolTerm = f.toPureFolTerm := by
  unfold toPureFolTerm
  simp only [normalize_eq_of_equiv h]

theorem toPureFolFormula_equiv {e f : FirstOrderCompatibleExpr prop} (h : Equiv e.term f.term) :
    e.toPureFolFormula = f.toPureFolFormula := by
  unfold toPureFolFormula
  simp only [normalize_eq_of_equiv h]
end FirstOrderCompatibleExpr

/-- Assign an expression with no dangling bound indices to each source leaf.
Images may contain free individual and proposition names. -/
structure FirstOrderAssignment where
  bound : (s : LSort) → Nat → FirstOrderCompatibleExpr s
  free : (s : LSort) → Identifier → FirstOrderCompatibleExpr s
  const : (s : LSort) → Identifier → FirstOrderCompatibleExpr s

namespace FirstOrderAssignment
/-- Preserve every admitted first-order and logical constant literally. -/
def FixesConstants (R : FirstOrderAssignment) : Prop :=
  ∀ s c (h : FirstOrderShape.AllowedConstant s c), R.const s c = FirstOrderCompatibleExpr.constant c h

def replacement (R : FirstOrderAssignment) : SymbolSubstitution where
  bound s n := (R.bound s n).term
  free s x := (R.free s x).term
  const s c := (R.const s c).term

private theorem replacement_language (R : SymbolSubstitution)
    (hb : ∀ s n, Compatible (R.bound s n))
    (hf : ∀ s x, Compatible (R.free s x))
    (hc : ∀ s c, Compatible (R.const s c)) (e : Term s) : Compatible (R.apply e) := by
  induction e generalizing R with
  | bound n => exact hb _ n
  | free x => exact hf _ x
  | const c => exact hc _ c
  | app f a ihf iha => exact .app (ihf R hb hf hc) (iha R hb hf hc)
  | lam b e ih =>
      apply Compatible.lam
      apply ih (R.lift b)
      · intro s n
        by_cases h : s = b
        · subst s; cases n with
          | zero => simpa only [SymbolSubstitution.lift, Sub.lift_zero] using (Compatible.bound (s := b) 0)
          | succ n => simpa only [SymbolSubstitution.lift, Sub.lift_succ] using (hb b n).rename (Ren.shift b)
        · simpa [SymbolSubstitution.lift, Sub.lift_other h] using (hb s n).rename (Ren.shift b)
      · intro s x; exact (hf s x).rename _
      · intro s c; exact (hc s c).rename _

theorem apply_subst_eq (R : FirstOrderAssignment) (e : Term s) (σ : Sub) :
    (R.replacement.apply e).subst σ = R.replacement.apply e := by
  rw [← SymbolSubstitution.apply_ofSub, SymbolSubstitution.apply_apply]
  have h : (SymbolSubstitution.ofSub σ).comp R.replacement = R.replacement := by
    apply SymbolSubstitution.ext
    · funext s n; simpa only [SymbolSubstitution.comp, replacement, SymbolSubstitution.apply_ofSub] using (R.bound s n).subst_eq σ
    · funext s x; simpa only [SymbolSubstitution.comp, replacement, SymbolSubstitution.apply_ofSub] using (R.free s x).subst_eq σ
    · funext s c; simpa only [SymbolSubstitution.comp, replacement, SymbolSubstitution.apply_ofSub] using (R.const s c).subst_eq σ
  rw [h]

def apply (R : FirstOrderAssignment) (e : Term s) : FirstOrderCompatibleExpr s where
  term := R.replacement.apply e
  language := replacement_language _ (fun s n => (R.bound s n).language)
    (fun s x => (R.free s x).language) (fun s c => (R.const s c).language) e
  subst_eq := R.apply_subst_eq e

def extend (R : FirstOrderAssignment) (a : FirstOrderCompatibleExpr b) : FirstOrderAssignment :=
  { R with bound := fun s n => if h : s = b then
      match n with
      | 0 => h.symm ▸ a
      | n + 1 => R.bound s n
    else R.bound s n }

@[simp] theorem extend_zero (R : FirstOrderAssignment) (a : FirstOrderCompatibleExpr b) :
    (R.extend a).bound b 0 = a := by simp [extend]
@[simp] theorem extend_succ (R : FirstOrderAssignment) (a : FirstOrderCompatibleExpr b) :
    (R.extend a).bound b (n + 1) = R.bound b n := by simp [extend]
@[simp] theorem extend_other (R : FirstOrderAssignment) (a : FirstOrderCompatibleExpr b) (h : s ≠ b) :
    (R.extend a).bound s n = R.bound s n := by simp [extend, h]

private theorem equiv_of_eq {e f : Term s} (h : e = f) : AlphaBetaEtaNormalization.Equiv e f := h ▸ .refl e

theorem apply_lam (R : FirstOrderAssignment) (e : Term t) (a : FirstOrderCompatibleExpr s) :
    Equiv ((R.apply (.lam s e)).app a).term ((R.extend a).apply e).term := by
  apply AlphaBetaEtaNormalization.Equiv.trans (AlphaBetaEtaNormalization.Equiv.beta _ a.term)
  apply equiv_of_eq
  change ((R.replacement.lift s).apply e).instantiate a.term = (R.extend a).replacement.apply e
  simp only [Term.instantiate, ← SymbolSubstitution.apply_ofSub, SymbolSubstitution.apply_apply]
  congr 1
  apply SymbolSubstitution.ext
  · funext u n
    simp only [SymbolSubstitution.comp, SymbolSubstitution.lift, SymbolSubstitution.apply_ofSub]
    change ((R.replacement.bound.lift s u n).instantiate a.term) = _
    by_cases h : u = s
    · subst u; cases n with
      | zero => simp [Term.instantiate, Term.single, Term.subst, replacement]
      | succ n => simp only [Sub.lift_succ, Term.shift_instantiate, replacement, extend_succ]
    · simp only [Sub.lift_other h, Term.shift_instantiate, replacement, extend_other R a h]
  · funext u x
    simpa only [SymbolSubstitution.comp, SymbolSubstitution.lift, SymbolSubstitution.apply_ofSub,
      replacement, extend] using (R.free u x).term.shift_instantiate a.term
  · funext u c
    simpa only [SymbolSubstitution.comp, SymbolSubstitution.lift, SymbolSubstitution.apply_ofSub,
      replacement, extend] using (R.const u c).term.shift_instantiate a.term
end FirstOrderAssignment

noncomputable instance : DecidableEq (PureFol.Formula PureFolTranslation.language) := Classical.decEq _

namespace FirstOrderCompatibleExpr

def neg (p : FirstOrderCompatibleExpr prop) : FirstOrderCompatibleExpr prop := (constant _ .neg).app p
def and (p q : FirstOrderCompatibleExpr prop) : FirstOrderCompatibleExpr prop := ((constant _ .and).app p).app q
def or (p q : FirstOrderCompatibleExpr prop) : FirstOrderCompatibleExpr prop := ((constant _ .or).app p).app q
def imp (p q : FirstOrderCompatibleExpr prop) : FirstOrderCompatibleExpr prop := ((constant _ .imp).app p).app q
def iff (p q : FirstOrderCompatibleExpr prop) : FirstOrderCompatibleExpr prop := ((constant _ .iff).app p).app q
def equal (t u : FirstOrderCompatibleExpr ind) : FirstOrderCompatibleExpr prop := ((constant _ .eq).app t).app u

-- At ground sorts, normalization is evaluation at depth zero.
private theorem toPureFolFormula_eval (p : FirstOrderCompatibleExpr prop) :
    PureFolTranslation.fromNormalFormula? (fun _ => none) (eval p.term ambient Depth.zero) = some p.toPureFolFormula :=
  p.toPureFolFormula_spec
private theorem toPureFolTerm_eval (t : FirstOrderCompatibleExpr ind) :
    PureFolTranslation.fromNormalTerm? (fun _ => none) (eval t.term ambient Depth.zero) = some t.toPureFolTerm :=
  t.toPureFolTerm_spec

@[simp] theorem toPureFolFormula_neg (p : FirstOrderCompatibleExpr prop) :
    (neg p).toPureFolFormula = .not p.toPureFolFormula := by
  apply Option.some.inj
  simpa only [neg, app, constant, normalize, eval, quote, reflect, readback,
    PureFolTranslation.fromNormalFormula?, toPureFolFormula_eval p, Option.bind_some] using (neg p).toPureFolFormula_spec.symm

@[simp] theorem toPureFolFormula_and (p q : FirstOrderCompatibleExpr prop) :
    (and p q).toPureFolFormula = .and p.toPureFolFormula q.toPureFolFormula := by
  apply Option.some.inj
  simpa only [and, app, constant, normalize, eval, quote, reflect, readback,
    PureFolTranslation.fromNormalFormula?, toPureFolFormula_eval p, toPureFolFormula_eval q, Option.bind_some] using (and p q).toPureFolFormula_spec.symm

@[simp] theorem toPureFolFormula_or (p q : FirstOrderCompatibleExpr prop) :
    (or p q).toPureFolFormula = .or p.toPureFolFormula q.toPureFolFormula := by
  apply Option.some.inj
  simpa only [or, app, constant, normalize, eval, quote, reflect, readback,
    PureFolTranslation.fromNormalFormula?, toPureFolFormula_eval p, toPureFolFormula_eval q, Option.bind_some] using (or p q).toPureFolFormula_spec.symm

@[simp] theorem toPureFolFormula_imp (p q : FirstOrderCompatibleExpr prop) :
    (imp p q).toPureFolFormula = .imp p.toPureFolFormula q.toPureFolFormula := by
  apply Option.some.inj
  simpa only [imp, app, constant, normalize, eval, quote, reflect, readback,
    PureFolTranslation.fromNormalFormula?, toPureFolFormula_eval p, toPureFolFormula_eval q, Option.bind_some] using (imp p q).toPureFolFormula_spec.symm

@[simp] theorem toPureFolFormula_iff (p q : FirstOrderCompatibleExpr prop) :
    (iff p q).toPureFolFormula = .iff p.toPureFolFormula q.toPureFolFormula := by
  apply Option.some.inj
  simpa only [iff, app, constant, normalize, eval, quote, reflect, readback,
    PureFolTranslation.fromNormalFormula?, toPureFolFormula_eval p, toPureFolFormula_eval q, Option.bind_some] using (iff p q).toPureFolFormula_spec.symm

@[simp] theorem toPureFolFormula_equal (t u : FirstOrderCompatibleExpr ind) :
    (equal t u).toPureFolFormula = .equal t.toPureFolTerm u.toPureFolTerm := by
  apply Option.some.inj
  simpa only [equal, app, constant, normalize, eval, quote, reflect, readback,
    PureFolTranslation.fromNormalFormula?, toPureFolTerm_eval t, toPureFolTerm_eval u, Option.bind_some] using (equal t u).toPureFolFormula_spec.symm

end FirstOrderCompatibleExpr

end Lisa.LambdaFol
