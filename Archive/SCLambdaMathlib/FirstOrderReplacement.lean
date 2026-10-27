import Lisa.SCLambdaToPure.FirstOrderNormalization
import Lisa.SCLambdaToPure.NamedReplacement
import Lisa.SCLambdaToPure.Grounding

/-! First-order replacements commute with normalization once the result has
first-order shape. These are syntactic equalities, not extra conversion axioms. -/

namespace Lisa.SCLambdaToPure.Replacement

open Lambda FirstOrderShape

theorem apply_default (R : Replacement) (hc : ∀ s c, R.const s c = .const c) (s : LSort) :
    R.apply (Grounding.defaultTerm s) = Grounding.defaultTerm s := by
  induction s generalizing R with
  | ind => exact hc _ _
  | prop => exact hc _ _
  | arrow s t _ ih =>
      change Term.lam s ((R.lift s).apply (Grounding.defaultTerm t)) = _
      rw [ih (R.lift s) (by intros; simp [lift, hc, Term.rename])]
      rfl

/-- Grounding commutes with replacements that only change individual leaves. -/
theorem ground_apply (R : Replacement) (e : Term s)
    (hb : ∀ s n, Grounding.ground (R.bound s n) = R.bound s n)
    (hi : ∀ x, Grounding.ground (R.free ind x) = R.free ind x)
    (hf : ∀ s, s ≠ ind → ∀ x, R.free s x = .free x)
    (hc : ∀ s c, R.const s c = .const c) :
    Grounding.ground (R.apply e) = R.apply (Grounding.ground e) := by
  induction e generalizing R with
  | bound n => exact hb _ n
  | @free s x =>
      cases s with
      | ind => exact hi x
      | prop => simp [apply, hf prop (by decide), Grounding.ground,
          Grounding.Symbols.apply, Grounding.symbols, Grounding.free]
      | arrow s t =>
          rw [show R.apply (.free (s := s >> t) x) = .free x from hf _ (by simp) x]
          exact (apply_default R hc _).symm
  | @const s c =>
      rw [show R.apply (.const (s := s) c) = .const c from hc s c]
      change Grounding.const _ c = R.apply (Grounding.const _ c)
      unfold Grounding.const
      split
      · exact (hc _ c).symm
      · exact (apply_default R hc _).symm
  | app f a ihf iha => exact congrArg₂ Term.app (ihf R hb hi hf hc) (iha R hb hi hf hc)
  | lam b e ih =>
      simp only [apply, Grounding.ground_lam]
      congr 1
      apply ih
      · intro s n
        change Grounding.ground (R.bound.lift b s n) = R.bound.lift b s n
        by_cases h : s = b
        · subst s; cases n with
          | zero => simp [Grounding.ground, Grounding.Symbols.apply]
          | succ n => simpa only [Sub.lift_succ, Grounding.symbols.rename] using
              congrArg (Term.rename (Ren.shift b)) (hb b n)
        · simpa only [Sub.lift_other h, Grounding.symbols.rename] using
            congrArg (Term.rename (Ren.shift b)) (hb s n)
      · intro x
        simpa only [lift, Grounding.symbols.rename] using
          congrArg (Term.rename (Ren.shift b)) (hi x)
      · intro s hs x; simp [lift, hf s hs, Term.rename]
      · intro s c; simp [lift, hc, Term.rename]

/-- Individual leaves may become terms; logical constants and proposition
names are retained. No requirement is made on unused higher-order free leaves. -/
structure FirstOrder (R : Replacement) : Prop where
  bound : ∀ n, Individual (R.bound ind n)
  free : ∀ x, Individual (R.free ind x)
  proposition : ∀ x, R.free prop x = .free x
  const : ∀ s c, R.const s c = .const c

theorem FirstOrder.lift (h : FirstOrder R) (b : LSort) : FirstOrder (R.lift b) where
  bound := by
    intro n
    by_cases hb : ind = b
    · subst b; cases n with
      | zero => simpa [Replacement.lift] using Individual.bound 0
      | succ n => simpa [Replacement.lift] using (h.bound n).rename (Ren.shift ind)
    · simpa [Replacement.lift, Sub.lift_other hb] using (h.bound n).rename (Ren.shift b)
  free x := (h.free x).rename _
  proposition := by intro x; simp [Replacement.lift, h.proposition, Term.rename]
  const := by intro s c; simp [Replacement.lift, h.const, Term.rename]

theorem individual (hR : FirstOrder R) {e : Term s} (h : Individual e) :
    Individual (R.apply e) := by
  induction h with
  | bound n => exact hR.bound n
  | free x => exact hR.free x
  | symbol n c => simpa [apply, hR.const] using Individual.symbol n c
  | app _ _ ihf iha => exact .app ihf iha

theorem formula (hR : FirstOrder R) {e : Term s} (h : Formula e) :
    Formula (R.apply e) := by
  induction h generalizing R with
  | free x => simpa [apply, hR.proposition] using Formula.free x
  | symbol n c => simpa [apply, hR.const] using Formula.symbol n c
  | top => simpa [apply, hR.const] using Formula.top
  | bot => simpa [apply, hR.const] using Formula.bot
  | app _ ha ih => exact .app (ih hR) (individual hR ha)
  | neg _ ih => simpa [apply, hR.const] using Formula.neg (ih hR)
  | and _ _ ihp ihq => simpa [apply, hR.const] using Formula.and (ihp hR) (ihq hR)
  | or _ _ ihp ihq => simpa [apply, hR.const] using Formula.or (ihp hR) (ihq hR)
  | imp _ _ ihp ihq => simpa [apply, hR.const] using Formula.imp (ihp hR) (ihq hR)
  | iff _ _ ihp ihq => simpa [apply, hR.const] using Formula.iff (ihp hR) (ihq hR)
  | eq ht hu => simpa [apply, hR.const] using Formula.eq (individual hR ht) (individual hR hu)
  | all _ ih => simpa [apply, hR.const] using Formula.all (ih (hR.lift ind))
  | ex _ ih => simpa [apply, hR.const] using Formula.ex (ih (hR.lift ind))

theorem normalize_formula (hR : FirstOrder R) {e : Term prop} (h : Formula (normalize e)) :
    normalize (R.apply e) = R.apply (normalize e) := by
  rw [normalize_eq_of_equiv (R.equiv (normalize_sound e))]
  exact normalize_formula_eq (formula hR h)

theorem normalize_individual (hR : FirstOrder R) {e : Term ind} (h : Individual (normalize e)) :
    normalize (R.apply e) = R.apply (normalize e) := by
  rw [normalize_eq_of_equiv (R.equiv (normalize_sound e))]
  exact normalize_individual_eq (individual hR h)

theorem abstract_firstOrder (x : SVar) (hx : x.sort = ind) : FirstOrder (abstract x) where
  bound n := .bound _
  free := by
    intro y
    change Individual (Names.free.bind x ⟨y, ind⟩)
    by_cases h : SVar.mk y ind = x
    · subst x; simp only [Names.bind_self]; exact .bound _
    · simp only [Names.bind_other _ h, Names.free, Term.rename]
      exact .free _
  proposition := by
    intro y
    have h : SVar.mk y prop ≠ x := by
      intro h; have hs := congrArg SVar.sort h; simp [hx] at hs
    simp [abstract, Names.bind_other _ h, Names.free, Term.rename]
  const _ _ := rfl

theorem single_firstOrder (x : SVar) (a : Term x.sort) (hx : x.sort = ind)
    (ha : Individual (hx ▸ a : Term ind)) : FirstOrder (single x a) where
  bound n := .bound n
  free := by
    intro y
    change Individual (if h : SVar.mk y ind = x then cast (congrArg Term (congrArg SVar.sort h).symm) a else .free y)
    split
    · rename_i he
      subst x
      exact ha
    · exact .free _
  proposition := by
    intro y
    have h : SVar.mk y prop ≠ x := by
      intro h; have hs := congrArg SVar.sort h; simp [hx] at hs
    simp [single, h]
  const _ _ := rfl

end Lisa.SCLambdaToPure.Replacement
