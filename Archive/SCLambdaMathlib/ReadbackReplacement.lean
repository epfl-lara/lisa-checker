import Lisa.SCLambdaToPure.Readback
import Lisa.SCLambdaToPure.FirstOrderReplacement

/-! Compatibility of first-order reading with capture-avoiding replacement. -/

namespace Lisa.SCLambdaToPure.Readback

open FirstOrder Lambda

private theorem get_map_heq {α β : Type} (f : α → β) (ts : List α) :
    HEq (fun i => f (ts.get i)) (ts.map f).get := by
  apply (Fin.heq_fun_iff (List.length_map (f := f) (as := ts)).symm).mpr
  intro i
  simp

private theorem func_map (f : BTerm n → BTerm m)
    (hf : ∀ a (c : Symbol) (ts : Fin a → BTerm n),
      f (.func c ts) = .func c (fun i => f (ts i))) (c : Symbol) (ts : List (BTerm n)) :
    f (.func c ts.get) = .func c (ts.map f).get := by
  rw [hf]
  simp only [Language.Term.func.injEq]
  exact ⟨(List.length_map (f := f) (as := ts)).symm, HEq.rfl, get_map_heq f ts⟩

/-- Reading a term commutes with any map preserving first-order function symbols,
provided it agrees on the individual leaves. The second conclusion handles the
partially applied heads used by the reader. -/
theorem reads_replace (R : Replacement) (hR : PreservesHeads R)
    (ρ : Bound n) (τ : Bound m) (f : BTerm n → BTerm m)
    (hf : ∀ a (c : Symbol) (ts : Fin a → BTerm n),
      f (.func c ts) = .func c (fun i => f (ts i)))
    (hb : ∀ i, term τ (R.bound ind i) = (term ρ (.bound i)).map f)
    (hv : ∀ x, term τ (R.free ind x) = (term ρ (.free x)).map f)
    (e : Term s) :
    (∀ h : s = ind, term τ (h ▸ R.apply e) = (term ρ (h ▸ e)).map f) ∧
    (s ≠ ind → spine τ (R.apply e) = (spine ρ e).map (fun v => (v.1, v.2.map f))) := by
  induction e with
  | bound i =>
      constructor
      · intro h; subst_vars; exact hb i
      · intro h
        obtain ⟨j, hj⟩ := hR.bound _ h i
        simp [Replacement.apply, hj, spine]
  | @free s x =>
      constructor
      · intro h; subst s; exact hv x
      · intro h; simp [Replacement.apply, hR.free s h, spine]
  | const c =>
      constructor
      · intro h; subst_vars
        simp only [Replacement.apply, hR.const, term, Option.map_some, hf]
        congr 2; funext i; exact i.elim0
      · intro _; simp [Replacement.apply, hR.const, spine]
  | lam => exact ⟨by simp, by simp [Replacement.apply, spine]⟩
  | @app s t g a ihg iha =>
      cases s with
      | ind =>
          have hg := ihg.2 (by simp)
          have ha := iha.1 rfl
          constructor
          · intro h; subst t
            simp only [Replacement.apply, term, hg, ha]
            cases spine ρ g with
            | none => rfl
            | some v =>
                obtain ⟨c, ts⟩ := v
                cases term ρ a <;> simp [func_map f hf, -Language.Term.func.injEq]
                apply congrArg (fun us : List (BTerm m) => Language.Term.func c us.get)
                simp
          · intro _
            simp only [Replacement.apply, spine, hg, ha]
            cases spine ρ g with
            | none => rfl
            | some v =>
                obtain ⟨c, ts⟩ := v
                cases term ρ a <;> simp
      | prop | arrow =>
          constructor
          · intro h; subst t; simp [Replacement.apply, term]
          · intro _; simp [Replacement.apply, spine]

theorem term_replace (R : Replacement) (hR : PreservesHeads R)
    (ρ : Bound n) (τ : Bound m) (f : BTerm n → BTerm m)
    (hf : ∀ a (c : Symbol) (ts : Fin a → BTerm n),
      f (.func c ts) = .func c (fun i => f (ts i)))
    (hb : ∀ i, term τ (R.bound ind i) = (term ρ (.bound i)).map f)
    (hv : ∀ x, term τ (R.free ind x) = (term ρ (.free x)).map f)
    (e : Term ind) : term τ (R.apply e) = (term ρ e).map f :=
  (reads_replace R hR ρ τ f hf hb hv e).1 rfl

private theorem apply_eq_const (R : Replacement) (hR : PreservesHeads R)
    (hs : s ≠ ind) (e : Term s) (c : Identifier) :
    R.apply e = .const c ↔ e = .const c := by
  cases e with
  | bound i =>
      obtain ⟨j, hj⟩ := hR.bound s hs i
      simp [Replacement.apply, hj]
  | free x => simp [Replacement.apply, hR.free s hs]
  | const d => simp [Replacement.apply, hR.const]
  | app | lam => simp [Replacement.apply]

private theorem not_eq_head (R : Replacement) (hR : PreservesHeads R)
    (e : Term (ind >> prop))
    (h : ∀ a : Term ind, e ≠ .app (.const ⟨"eq", 0⟩) a) :
    ∀ a : Term ind, R.apply e ≠ .app (.const ⟨"eq", 0⟩) a := by
  intro a ha
  cases e with
  | bound i =>
      obtain ⟨j, hj⟩ := hR.bound (ind >> prop) (by simp) i
      simp [Replacement.apply, hj] at ha
  | free x => simp [Replacement.apply, hR.free (ind >> prop) (by simp)] at ha
  | const d => simp [Replacement.apply, hR.const] at ha
  | lam => simp [Replacement.apply] at ha
  | @app s f t =>
      simp only [Replacement.apply, Term.app.injEq] at ha
      obtain ⟨rfl, hf, _⟩ := ha
      have hf' : t = .const ⟨"eq", 0⟩ :=
        (apply_eq_const R hR (by simp) t _).mp (eq_of_heq hf)
      exact h _ (by rw [hf'])

/-- Apply a family of maps on terms to all atoms, retaining logical syntax.
The added prefix of bound levels accounts for abstraction of free names. -/
def mapTerms (k : Nat) (f : ∀ n, BTerm n → BTerm (k + n)) :
    {n : Nat} → BFormula n → BFormula (k + n)
  | _, .falsum => .falsum
  | _, .equal t u => .equal (f _ t) (f _ u)
  | _, .rel c ts => .rel c (fun i => f _ (ts i))
  | _, .imp p q => .imp (mapTerms k f p) (mapTerms k f q)
  | _, .all p => .all (mapTerms k f p)

theorem formula_replace (k : Nat) (R : Nat → Replacement)
    (hR : ∀ n, PreservesHeads (R n)) (hRl : ∀ n, R (n + 1) = (R n).lift ind)
    (ρ : ∀ n, Bound n) (τ : ∀ n, Bound (k + n))
    (hρ : ∀ n, ρ (n + 1) = bind (ρ n)) (hτ : ∀ n, τ (n + 1) = bind (τ n))
    (f : ∀ n, BTerm n → BTerm (k + n))
    (hf : ∀ n a (c : Symbol) (ts : Fin a → BTerm n),
      f n (.func c ts) = .func c (fun i => f n (ts i)))
    (hb : ∀ n i, term (τ n) ((R n).bound ind i) = (term (ρ n) (.bound i)).map (f n))
    (hv : ∀ n x, term (τ n) ((R n).free ind x) = (term (ρ n) (.free x)).map (f n))
    (n : Nat) (r : Bound n) (e : Term prop) (hr : r = ρ n)
    {p : BFormula n} (hp : formula r e = some p) :
    formula (τ n) ((R n).apply e) = some (mapTerms k f p) := by
  induction n, r, e using formula.induct with
  | case1 n r | case2 n r =>
      simp [formula] at hp
      subst p
      simp [Replacement.apply, (hR n).const, formula, mapTerms,
        Language.BoundedFormula.not, Top.top, Bot.bot]
  | case3 n r a ih =>
      cases ha : formula r a <;> simp [formula, ha] at hp
      subst p
      simp [Replacement.apply, (hR n).const, formula, ih hr ha,
        Language.BoundedFormula.not, mapTerms, Bot.bot]
  | case4 n r a b iha ihb | case5 n r a b iha ihb | case6 n r a b iha ihb | case7 n r a b iha ihb =>
      cases ha : formula r a <;> simp [formula, ha] at hp
      cases hb' : formula r b <;> simp [hb'] at hp
      subst p
      simp [Replacement.apply, (hR n).const, formula, iha hr ha, ihb hr hb',
        Language.BoundedFormula.not, Language.BoundedFormula.iff, Min.min, Max.max, mapTerms, Bot.bot]
  | case8 n r t u =>
      cases ht : term r t <;> simp [formula, ht] at hp
      cases hu : term r u <;> simp [hu] at hp
      subst p
      subst r
      simp [Replacement.apply, (hR n).const, formula, mapTerms,
        term_replace (R n) (hR n) (ρ n) (τ n) (f n) (hf n) (hb n) (hv n), ht, hu]
  | case9 n r a ih | case10 n r a ih =>
      cases ha : formula (bind r) a <;> simp [formula, ha] at hp
      subst p
      have hi := ih (by rw [hr, hρ]) ha
      rw [hτ, hRl] at hi
      simp [Replacement.apply, (hR n).const, formula, hi,
        Language.BoundedFormula.ex, Language.BoundedFormula.not, mapTerms, Bot.bot]
  | case11 n r x =>
      simp [formula] at hp
      subst p
      simp [Replacement.apply, (hR n).free prop (by decide), formula, mapTerms]
      funext i; exact i.elim0
  | case12 n r c htop hbot =>
      simp [formula] at hp
      subst p
      simp [Replacement.apply, (hR n).const, formula, mapTerms]
      funext i; exact i.elim0
  | case13 n r g a h =>
      have hg := not_eq_head (R n) (hR n) g h
      cases hg' : spine r g with
      | none => simp [formula, hg'] at hp
      | some v =>
          obtain ⟨c, ts⟩ := v
          cases ha : term r a <;> simp [formula, hg', ha] at hp
          subst p
          subst r
          have hsp := (reads_replace (R n) (hR n) (ρ n) (τ n) (f n)
            (hf n) (hb n) (hv n) g).2 (by simp)
          rw [hg'] at hsp
          simp only [Option.map_some] at hsp
          simp only [Replacement.apply, formula, hsp,
            term_replace (R n) (hR n) (ρ n) (τ n) (f n) (hf n) (hb n) (hv n), ha,
            Option.map_some, mapTerms]
          apply congrArg some
          simp only [Language.BoundedFormula.rel.injEq]
          refine ⟨by simp, HEq.rfl, ?_⟩
          apply (Fin.heq_fun_iff (by simp)).mpr
          intro i
          obtain ⟨i, hi⟩ := i
          simp only [List.get_eq_getElem]
          simp only [← List.map_singleton, ← List.map_append, List.getElem_map]
  | case14 => simp_all [formula]

end Lisa.SCLambdaToPure.Readback
