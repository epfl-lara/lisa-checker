import Lisa.SCLambdaToPure.AToPure.Readback
import Lisa.SCLambdaToPure.AToPure.PureProofs

/-! A syntactic relation for the forward proof transformation.
At ground sorts it consists of first-order derivations; at arrow sorts it
requires preservation of related arguments. No models or validity predicates
are used. The fundamental lemma below is conditional on related interpretations
of the source symbols; logical constants must satisfy that condition separately.
-/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda
open FirstOrderShape (InLanguage)

/-- Lambda syntax over the first-order signature, before normalization, with no
dangling bound indices. Free individual and proposition names are allowed. -/
structure ScopedExpr (s : LSort) where
  term : Term s
  language : InLanguage term
  /-- Substitution of ambient bound indices has no effect. -/
  subst_eq : ∀ σ, term.subst σ = term

namespace ScopedExpr
def app (f : ScopedExpr (s >> t)) (a : ScopedExpr s) : ScopedExpr t where
  term := .app f.term a.term
  language := .app f.language a.language
  subst_eq σ := congrArg₂ Term.app (f.subst_eq σ) (a.subst_eq σ)

def individual (x : Identifier) : ScopedExpr ind := ⟨.free x, .individual x, by intros; rfl⟩
def proposition (x : Identifier) : ScopedExpr prop := ⟨.free x, .proposition x, by intros; rfl⟩
def constant (c : Identifier) (h : FirstOrderShape.Constant s c) : ScopedExpr s :=
  ⟨.const c, .const h, by intros; rfl⟩

def readTerm (e : ScopedExpr ind) : Pure.Term Readback.language :=
  (Readback.term (fun _ => none) (normalize e.term)).get
    (Readback.term_isSome (FirstOrderShape.normalize_individual e.language e.subst_eq)
      (normalize_supported e.term e.subst_eq) _ (by simp [Depth.zero]))

def readFormula (e : ScopedExpr prop) : Pure.Formula Readback.language :=
  (Readback.formula (fun _ => none) (normalize e.term)).get
    (Readback.formula_isSome (FirstOrderShape.normalize_formula e.language e.subst_eq)
      (normalize_supported e.term e.subst_eq) _ (by simp [Depth.zero]))

theorem readTerm_spec (e : ScopedExpr ind) :
    Readback.term (fun _ => none) (normalize e.term) = some e.readTerm := by
  simp [readTerm]

theorem readFormula_spec (e : ScopedExpr prop) :
    Readback.formula (fun _ => none) (normalize e.term) = some e.readFormula := by
  simp [readFormula]

theorem readTerm_equiv {e f : ScopedExpr ind} (h : Equiv e.term f.term) :
    e.readTerm = f.readTerm := by
  unfold readTerm
  simp only [normalize_eq_of_equiv h]

theorem readFormula_equiv {e f : ScopedExpr prop} (h : Equiv e.term f.term) :
    e.readFormula = f.readFormula := by
  unfold readFormula
  simp only [normalize_eq_of_equiv h]
end ScopedExpr

/-- Substituting complete expressions for every leaf closes any source term. -/
structure Assignment where
  bound : (s : LSort) → Nat → ScopedExpr s
  free : (s : LSort) → Identifier → ScopedExpr s
  const : (s : LSort) → Identifier → ScopedExpr s

namespace Assignment
def replacement (R : Assignment) : Replacement where
  bound s n := (R.bound s n).term
  free s x := (R.free s x).term
  const s c := (R.const s c).term

private theorem replacement_language (R : Replacement)
    (hb : ∀ s n, InLanguage (R.bound s n))
    (hf : ∀ s x, InLanguage (R.free s x))
    (hc : ∀ s c, InLanguage (R.const s c)) (e : Term s) : InLanguage (R.apply e) := by
  induction e generalizing R with
  | bound n => exact hb _ n
  | free x => exact hf _ x
  | const c => exact hc _ c
  | app f a ihf iha => exact .app (ihf R hb hf hc) (iha R hb hf hc)
  | lam b e ih =>
      apply InLanguage.lam
      apply ih (R.lift b)
      · intro s n
        by_cases h : s = b
        · subst s; cases n with
          | zero => simpa only [Replacement.lift, Sub.lift_zero] using (InLanguage.bound (s := b) 0)
          | succ n => simpa only [Replacement.lift, Sub.lift_succ] using (hb b n).rename (Ren.shift b)
        · simpa [Replacement.lift, Sub.lift_other h] using (hb s n).rename (Ren.shift b)
      · intro s x; exact (hf s x).rename _
      · intro s c; exact (hc s c).rename _

theorem apply_subst_eq (R : Assignment) (e : Term s) (σ : Sub) :
    (R.replacement.apply e).subst σ = R.replacement.apply e := by
  rw [← Replacement.apply_ofSub, Replacement.apply_apply]
  have h : (Replacement.ofSub σ).comp R.replacement = R.replacement := by
    apply Replacement.ext
    · funext s n; simpa only [Replacement.comp, replacement, Replacement.apply_ofSub] using (R.bound s n).subst_eq σ
    · funext s x; simpa only [Replacement.comp, replacement, Replacement.apply_ofSub] using (R.free s x).subst_eq σ
    · funext s c; simpa only [Replacement.comp, replacement, Replacement.apply_ofSub] using (R.const s c).subst_eq σ
  rw [h]

def apply (R : Assignment) (e : Term s) : ScopedExpr s where
  term := R.replacement.apply e
  language := replacement_language _ (fun s n => (R.bound s n).language)
    (fun s x => (R.free s x).language) (fun s c => (R.const s c).language) e
  subst_eq := R.apply_subst_eq e

def extend (R : Assignment) (a : ScopedExpr b) : Assignment :=
  { R with bound := fun s n => if h : s = b then
      match n with
      | 0 => h.symm ▸ a
      | n + 1 => R.bound s n
    else R.bound s n }

@[simp] theorem extend_zero (R : Assignment) (a : ScopedExpr b) :
    (R.extend a).bound b 0 = a := by simp [extend]
@[simp] theorem extend_succ (R : Assignment) (a : ScopedExpr b) :
    (R.extend a).bound b (n + 1) = R.bound b n := by simp [extend]
@[simp] theorem extend_other (R : Assignment) (a : ScopedExpr b) (h : s ≠ b) :
    (R.extend a).bound s n = R.bound s n := by simp [extend, h]

private theorem equiv_of_eq {e f : Term s} (h : e = f) : Lambda.Equiv e f := h ▸ .refl e

theorem apply_lam (R : Assignment) (e : Term t) (a : ScopedExpr s) :
    Equiv ((R.apply (.lam s e)).app a).term ((R.extend a).apply e).term := by
  apply Lambda.Equiv.trans (Lambda.Equiv.beta _ a.term)
  apply equiv_of_eq
  change ((R.replacement.lift s).apply e).instantiate a.term = (R.extend a).replacement.apply e
  simp only [Term.instantiate, ← Replacement.apply_ofSub, Replacement.apply_apply]
  congr 1
  apply Replacement.ext
  · funext u n
    simp only [Replacement.comp, Replacement.lift, Replacement.apply_ofSub]
    change ((R.replacement.bound.lift s u n).instantiate a.term) = _
    by_cases h : u = s
    · subst u; cases n with
      | zero => simp [Term.instantiate, Term.single, Term.subst, replacement]
      | succ n => simp only [Sub.lift_succ, Term.shift_instantiate, replacement, extend_succ]
    · simp only [Sub.lift_other h, Term.shift_instantiate, replacement, extend_other R a h]
  · funext u x
    simpa only [Replacement.comp, Replacement.lift, Replacement.apply_ofSub,
      replacement, extend] using (R.free u x).term.shift_instantiate a.term
  · funext u c
    simpa only [Replacement.comp, Replacement.lift, Replacement.apply_ofSub,
      replacement, extend] using (R.const u c).term.shift_instantiate a.term
end Assignment

noncomputable instance : DecidableEq (Pure.Formula Readback.language) := Classical.decEq _

/-- Relate syntax using derivations at ground sorts and applications at arrow sorts. -/
def Related (Γ Δ : Pure.Context Readback.language) :
    (s : LSort) → ScopedExpr s → ScopedExpr s → Prop
  | .ind, e, f => Pure.Provable Γ (insert (.equal e.readTerm f.readTerm) Δ)
  | .prop, e, f => Pure.Provable Γ (insert (.iff e.readFormula f.readFormula) Δ)
  | .arrow s t, e, f => ∀ a b, Related Γ Δ s a b → Related Γ Δ t (e.app a) (f.app b)

theorem Related.convert {e e' f f' : ScopedExpr s}
    (he : Equiv e.term e'.term) (hf : Equiv f.term f'.term)
    (h : Related Γ Δ s e f) : Related Γ Δ s e' f' := by
  induction s with
  | ind => simpa only [Related, ScopedExpr.readTerm_equiv he, ScopedExpr.readTerm_equiv hf] using h
  | prop => simpa only [Related, ScopedExpr.readFormula_equiv he, ScopedExpr.readFormula_equiv hf] using h
  | arrow s t ihs iht =>
      intro a b hab
      exact iht (.app he (.refl _)) (.app hf (.refl _)) (h a b hab)

private theorem related_symmetric_transitive (s : LSort) :
    (∀ e f, Related Γ Δ s e f → Related Γ Δ s f e) ∧
    (∀ e f g, Related Γ Δ s e f → Related Γ Δ s f g → Related Γ Δ s e g) := by
  induction s with
  | ind =>
      constructor
      · intro e f ⟨d⟩; exact ⟨d.eq_symm⟩
      · intro e f g ⟨d⟩ ⟨h⟩; exact ⟨d.eq_trans h⟩
  | prop =>
      constructor
      · intro e f ⟨d⟩; exact ⟨d.iff_symm⟩
      · intro e f g ⟨d⟩ ⟨h⟩; exact ⟨d.iff_trans h⟩
  | arrow s t ihs iht =>
      constructor
      · intro e f h a b hab
        exact iht.1 _ _ (h b a (ihs.1 _ _ hab))
      · intro e f g h₁ h₂ a b hab
        have hbb := ihs.2 _ _ _ (ihs.1 _ _ hab) hab
        exact iht.2 _ _ _ (h₁ a b hab) (h₂ b b hbb)

theorem Related.symm {e f : ScopedExpr s} (h : Related Γ Δ s e f) :
    Related Γ Δ s f e := (related_symmetric_transitive s).1 _ _ h

theorem Related.trans {e f g : ScopedExpr s}
    (h : Related Γ Δ s e f) (h' : Related Γ Δ s f g) : Related Γ Δ s e g :=
  (related_symmetric_transitive s).2 _ _ _ h h'

structure RelatedAssignments (Γ Δ : Pure.Context Readback.language)
    (R S : Assignment) : Prop where
  bound : ∀ s n, Related Γ Δ s (R.bound s n) (S.bound s n)
  free : ∀ s x, Related Γ Δ s (R.free s x) (S.free s x)
  const : ∀ s c, Related Γ Δ s (R.const s c) (S.const s c)

theorem RelatedAssignments.extend (h : RelatedAssignments Γ Δ R S)
    (ha : Related Γ Δ s a b) : RelatedAssignments Γ Δ (R.extend a) (S.extend b) where
  bound u n := by
    by_cases hu : u = s
    · subst u; cases n
      · simpa only [Assignment.extend_zero] using ha
      · simpa only [Assignment.extend_succ] using h.bound s _
    · simpa only [Assignment.extend_other _ _ hu] using h.bound u n
  free := h.free
  const := h.const

/-- The fundamental lemma is an induction on syntax, including lambda binders.
It does not assume that normalization itself preserves provability.
-/
theorem fundamental (e : Term s) (h : RelatedAssignments Γ Δ R S) :
    Related Γ Δ s (R.apply e) (S.apply e) := by
  induction e generalizing R S with
  | bound n => exact h.bound _ n
  | free x => exact h.free _ x
  | const c => exact h.const _ c
  | app f a ihf iha => exact ihf h _ _ (iha h)
  | lam b e ih =>
      intro a a' ha
      exact Related.convert (R.apply_lam e a).symm (S.apply_lam e a').symm
        (ih (h.extend ha))

end Lisa.SCLambdaToPure.Syntactic

/-! The propositional constants and individual equality preserve the syntactic
relation, using only first-order proof rules. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda
namespace ScopedExpr

def neg (p : ScopedExpr prop) : ScopedExpr prop := (constant _ .neg).app p
def and (p q : ScopedExpr prop) : ScopedExpr prop := ((constant _ .and).app p).app q
def or (p q : ScopedExpr prop) : ScopedExpr prop := ((constant _ .or).app p).app q
def imp (p q : ScopedExpr prop) : ScopedExpr prop := ((constant _ .imp).app p).app q
def iff (p q : ScopedExpr prop) : ScopedExpr prop := ((constant _ .iff).app p).app q
def equal (t u : ScopedExpr ind) : ScopedExpr prop := ((constant _ .eq).app t).app u

-- At ground sorts, normalization is evaluation at depth zero.
private theorem readFormula_eval (p : ScopedExpr prop) :
    Readback.formula (fun _ => none) (eval p.term ambient Depth.zero) = some p.readFormula :=
  p.readFormula_spec
private theorem readTerm_eval (t : ScopedExpr ind) :
    Readback.term (fun _ => none) (eval t.term ambient Depth.zero) = some t.readTerm :=
  t.readTerm_spec

@[simp] theorem read_neg (p : ScopedExpr prop) :
    (neg p).readFormula = .not p.readFormula := by
  apply Option.some.inj
  simpa only [neg, app, constant, normalize, eval, quote, reflect, readback,
    Readback.formula, readFormula_eval p, Option.bind_some] using (neg p).readFormula_spec.symm

@[simp] theorem read_and (p q : ScopedExpr prop) :
    (and p q).readFormula = .and p.readFormula q.readFormula := by
  apply Option.some.inj
  simpa only [and, app, constant, normalize, eval, quote, reflect, readback,
    Readback.formula, readFormula_eval p, readFormula_eval q, Option.bind_some] using (and p q).readFormula_spec.symm

@[simp] theorem read_or (p q : ScopedExpr prop) :
    (or p q).readFormula = .or p.readFormula q.readFormula := by
  apply Option.some.inj
  simpa only [or, app, constant, normalize, eval, quote, reflect, readback,
    Readback.formula, readFormula_eval p, readFormula_eval q, Option.bind_some] using (or p q).readFormula_spec.symm

@[simp] theorem read_imp (p q : ScopedExpr prop) :
    (imp p q).readFormula = .imp p.readFormula q.readFormula := by
  apply Option.some.inj
  simpa only [imp, app, constant, normalize, eval, quote, reflect, readback,
    Readback.formula, readFormula_eval p, readFormula_eval q, Option.bind_some] using (imp p q).readFormula_spec.symm

@[simp] theorem read_iff (p q : ScopedExpr prop) :
    (iff p q).readFormula = .iff p.readFormula q.readFormula := by
  apply Option.some.inj
  simpa only [iff, app, constant, normalize, eval, quote, reflect, readback,
    Readback.formula, readFormula_eval p, readFormula_eval q, Option.bind_some] using (iff p q).readFormula_spec.symm

@[simp] theorem read_equal (t u : ScopedExpr ind) :
    (equal t u).readFormula = .equal t.readTerm u.readTerm := by
  apply Option.some.inj
  simpa only [equal, app, constant, normalize, eval, quote, reflect, readback,
    Readback.formula, readTerm_eval t, readTerm_eval u, Option.bind_some] using (equal t u).readFormula_spec.symm

end ScopedExpr

theorem related_neg : Related Γ Δ (prop >> prop)
    (ScopedExpr.constant _ .neg) (ScopedExpr.constant _ .neg) := by
  intro p q ⟨h⟩
  simpa only [Related, ← ScopedExpr.neg.eq_1, ScopedExpr.read_neg] using
    (show Pure.Provable Γ _ from ⟨h.not_congr⟩)

theorem related_and : Related Γ Δ (prop >> prop >> prop)
    (ScopedExpr.constant _ .and) (ScopedExpr.constant _ .and) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [Related, ← ScopedExpr.and.eq_1, ScopedExpr.read_and] using
    (show Pure.Provable Γ _ from ⟨hp.and_congr hq⟩)

theorem related_or : Related Γ Δ (prop >> prop >> prop)
    (ScopedExpr.constant _ .or) (ScopedExpr.constant _ .or) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [Related, ← ScopedExpr.or.eq_1, ScopedExpr.read_or] using
    (show Pure.Provable Γ _ from ⟨hp.or_congr hq⟩)

theorem related_imp : Related Γ Δ (prop >> prop >> prop)
    (ScopedExpr.constant _ .imp) (ScopedExpr.constant _ .imp) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [Related, ← ScopedExpr.imp.eq_1, ScopedExpr.read_imp] using
    (show Pure.Provable Γ _ from ⟨hp.imp_congr hq⟩)

theorem related_iff : Related Γ Δ (prop >> prop >> prop)
    (ScopedExpr.constant _ .iff) (ScopedExpr.constant _ .iff) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [Related, ← ScopedExpr.iff.eq_1, ScopedExpr.read_iff] using
    (show Pure.Provable Γ _ from ⟨hp.iff_congr hq⟩)

theorem related_equal : Related Γ Δ (ind >> ind >> prop)
    (ScopedExpr.constant _ .eq) (ScopedExpr.constant _ .eq) := by
  intro t t' ⟨ht⟩ u u' ⟨hu⟩
  simpa only [Related, ← ScopedExpr.equal.eq_1, ScopedExpr.read_equal] using
    (show Pure.Provable Γ _ from ⟨Pure.ProofTree.equal_congr ht hu⟩)

end Lisa.SCLambdaToPure.Syntactic
