import Lisa.SCLambdaToPure.AToPure.Readback
import Lisa.SCLambdaToPure.AToPure.PureOperations

/-! Reading commutes with capture-avoiding individual replacement.
The mutual reader induction covers formulas inside epsilon terms. It states
preservation of successful reads; unsupported source syntax is not required
to remain unsupported after a replacement. -/
namespace Lisa.SCLambdaToPure.Readback
open Lambda
open Pure (BTerm.subst BFormula.subst Substitution)

private theorem func_subst (σ : Substitution Readback.language Identifier n Identifier m)
    (c : Symbol) (ts : List (BTerm n)) :
    (Pure.BTerm.func c ts.get).subst σ =
      .func c (ts.map (fun t => t.subst σ)).get := by
  simp only [Pure.BTerm.subst, Pure.BTerm.func.injEq]
  refine ⟨(List.length_map ..).symm, HEq.rfl, ?_⟩
  apply (Fin.heq_fun_iff (by simp)).mpr
  intro i
  simp

private theorem rel_subst (σ : Substitution Readback.language Identifier n Identifier m)
    (c : Symbol) (ts : List (BTerm n)) :
    (Pure.BFormula.rel c ts.get).subst σ =
      .rel c (ts.map (fun t => t.subst σ)).get := by
  simp only [Pure.BFormula.subst, Pure.BFormula.rel.injEq]
  refine ⟨(List.length_map ..).symm, HEq.rfl, ?_⟩
  apply (Fin.heq_fun_iff (by simp)).mpr
  intro i
  simp

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

/-- A source replacement and a target substitution give the same readback when
they agree on leaves and lift together under an individual binder. The result
also includes application spines, which the term and atom readers share. -/
theorem reads_replace (k : Nat) (R : Nat → Replacement)
    (hR : ∀ n, PreservesHeads (R n)) (hRl : ∀ n, R (n + 1) = (R n).lift ind)
    (ρ : ∀ n, Bound n) (τ : ∀ n, Bound (k + n))
    (hρ : ∀ n, ρ (n + 1) = Readback.bind (ρ n))
    (hτ : ∀ n, τ (n + 1) = Readback.bind (τ n))
    (σ : ∀ n, Substitution Readback.language Identifier n Identifier (k + n))
    (hσ : ∀ n, σ (n + 1) = (σ n).lift)
    (hb : ∀ n i t, term (ρ n) (.bound i) = some t →
      term (τ n) ((R n).bound ind i) = some (t.subst (σ n)))
    (hv : ∀ n x t, term (ρ n) (.free x) = some t →
      term (τ n) ((R n).free ind x) = some (t.subst (σ n))) :
    (∀ n r e, r = ρ n → ∀ t, term r e = some t →
      term (τ n) ((R n).apply e) = some (t.subst (σ n))) ∧
    (∀ n r e, r = ρ n → ∀ p, formula r e = some p →
      formula (τ n) ((R n).apply e) = some (p.subst (σ n))) ∧
    (∀ s n r (e : Term s), r = ρ n → s ≠ ind → ∀ c ts,
      spine r e = some (c, ts) →
      spine (τ n) ((R n).apply e) = some (c, ts.map (fun t => t.subst (σ n)))) := by
  apply term.mutual_induct
  case case1 =>
    intro n r i hr t ht
    subst r
    exact hb n i t ht
  case case2 =>
    intro n r x hr t ht
    subst r
    exact hv n x t ht
  case case3 =>
    intro n r c _ t ht
    simp only [term, Option.some.injEq] at ht
    subst t
    simp only [Replacement.apply, (hR n).const, term, Pure.BTerm.subst]
    congr 2
    funext i
    exact i.elim0
  case case4 =>
    intro n r f a ihf iha hr t ht
    rcases hf : spine r f with _ | ⟨c, ts⟩ <;>
      simp [term, hf] at ht
    rcases ha : term r a with _ | u <;>
      simp [ha] at ht
    cases ht
    simp [Replacement.apply, term, ihf hr (by simp) _ _ hf, iha hr _ ha,
      func_subst, -Pure.BTerm.func.injEq]
    apply congrArg (fun us : List (BTerm (k + n)) => Pure.BTerm.func c us.get)
    simp
  case case5 =>
    intro n r p ih hr t ht
    rcases hp : formula (Readback.bind r) p with _ | q <;>
      simp [term, hp] at ht
    cases ht
    have hi := ih (by rw [hr, hρ]) q hp
    rw [hτ, hRl, hσ] at hi
    simp [Replacement.apply, (hR n).const, term, hi, Pure.BTerm.subst]
  -- Unsupported term syntax.
  case case6 | case7 =>
    intros
    simp_all [term]
  -- Truth and falsehood.
  case case8 | case9 =>
    intro n r _ p hp
    simp only [formula, Option.some.injEq] at hp
    subst p
    simp [Replacement.apply, (hR n).const, formula, Pure.BFormula.subst]
  case case10 =>
    intro n r p ih hr q hq
    cases hp : formula r p <;> simp [formula, hp] at hq
    subst q
    simp [Replacement.apply, (hR n).const, formula, ih hr _ hp, Pure.BFormula.subst]
  -- All four binary propositional connectives use the same argument.
  case case11 | case12 | case13 | case14 =>
    intro n r p q ihp ihq hr u hu
    cases hp : formula r p <;> simp [formula, hp] at hu
    cases hq : formula r q <;> simp [hq] at hu
    subst u
    simp [Replacement.apply, (hR n).const, formula, ihp hr _ hp, ihq hr _ hq, Pure.BFormula.subst]
  case case15 =>
    intro n r t u iht ihu hr p hp
    cases ht : term r t <;> simp [formula, ht] at hp
    cases hu : term r u <;> simp [hu] at hp
    subst p
    simp [Replacement.apply, (hR n).const, formula, iht hr _ ht, ihu hr _ hu, Pure.BFormula.subst]
  -- Universal and existential quantification.
  case case16 | case17 =>
    intro n r p ih hr q hq
    cases hp : formula (Readback.bind r) p <;> simp [formula, hp] at hq
    subst q
    have hi := ih (by rw [hr, hρ]) _ hp
    rw [hτ, hRl, hσ] at hi
    simp [Replacement.apply, (hR n).const, formula, hi, Pure.BFormula.subst]
  case case18 =>
    intro n r x _ p hp
    simp only [formula, Option.some.injEq] at hp
    subst p
    simp only [Replacement.apply, (hR n).free prop (by decide), formula, Pure.BFormula.subst]
    congr 2
    funext i
    exact i.elim0
  case case19 =>
    intro n r c ht hb _ p hp
    simp [formula] at hp
    subst p
    simp only [Replacement.apply, (hR n).const, formula, Pure.BFormula.subst]
    congr 2
    funext i
    exact i.elim0
  case case20 =>
    intro n r f a h ihf iha hr p hp
    have h' := not_eq_head (R n) (hR n) f h
    rcases hf : spine r f with _ | ⟨c, ts⟩ <;>
      simp [formula, hf] at hp
    rcases ha : term r a with _ | t <;>
      simp [ha] at hp
    subst p
    simp [Replacement.apply, formula, ihf hr (by simp) _ _ hf, iha hr _ ha,
      rel_subst, -Pure.BFormula.rel.injEq]
    apply congrArg (fun us : List (BTerm (k + n)) => Pure.BFormula.rel c us.get)
    simp
  case case21 =>
    intros
    simp_all [formula]
  case case22 =>
    intro s n r x _ hs c ts h
    simp only [spine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Replacement.apply, (hR n).free s hs, spine]
  case case23 =>
    intro s n r x _ _ c ts h
    simp only [spine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Replacement.apply, (hR n).const, spine]
  case case24 =>
    intro s n r f a ihf iha hr _ c ts h
    rcases hf : spine r f with _ | ⟨d, us⟩ <;>
      simp [spine, hf] at h
    rcases ha : term r a with _ | t <;>
      simp [ha] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Replacement.apply, spine, ihf hr (by simp) _ _ hf, iha hr _ ha]
  case case25 =>
    intros
    simp_all [spine]

end Lisa.SCLambdaToPure.Readback

/-! Readback commutes with abstraction of a free individual name and substitution
of an individual term. Both operations preserve inner quantifier and epsilon binders. -/
namespace Lisa.SCLambdaToPure.Readback
open Lambda
open Pure (Renaming)

def closeAt (x : Identifier) (n : Nat) : Renaming Identifier n Identifier (1 + n)
  | .inl y => if y = x then .inr ⟨0, by omega⟩ else .inl y
  | .inr i => .inr ⟨i + 1, by omega⟩

theorem closeAt_lift (x : Identifier) (n : Nat) : closeAt x (n + 1) = (closeAt x n).lift := by
  funext z
  cases z with
  | inl y =>
    by_cases h : y = x <;> simp [closeAt, Pure.Renaming.lift, Pure.shift, h]
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [closeAt, Pure.Renaming.lift, Pure.shift, Fin.ext_iff, Nat.add_comm]

private theorem abstract_bound (x : Identifier) (n i : Nat) (t : BTerm n)
    (ht : term (scope n) (.bound i) = some t) :
    term (scope (1 + n)) ((abstractAt x n).bound ind i) =
      some (t.subst (Pure.BTerm.var ∘ closeAt x n)) := by
  by_cases hi : i < n
  · simp only [term, scope, hi, ↓reduceDIte, Option.map_some, Option.some.injEq] at ht
    subst t
    simp [abstractAt, show ¬n ≤ i by omega, term, scope,
      show i < 1 + n by omega, closeAt, Pure.BTerm.subst, Fin.ext_iff]
    omega
  · simp [term, scope, hi] at ht

private theorem abstract_free (x y : Identifier) (n : Nat) (t : BTerm n)
    (ht : term (scope n) (.free y) = some t) :
    term (scope (1 + n)) ((abstractAt x n).free ind y) =
      some (t.subst (Pure.BTerm.var ∘ closeAt x n)) := by
  simp only [term, Option.some.injEq] at ht
  subst t
  by_cases h : y = x
  · subst y
    simp [abstractAt, term, scope, closeAt, Pure.BTerm.subst]
  · simp [abstractAt, h, term, closeAt, Pure.BTerm.subst]

private theorem closeAt_zero (x : Identifier) : closeAt x 0 = Pure.close x := by
  funext z
  cases z with
  | inl y => rfl
  | inr i => exact i.elim0

theorem formula_abstract {e : Term prop} {p : BFormula 0}
    (hp : formula (fun _ => none) e = some p) (x : Identifier) :
    formula (Readback.bind (fun _ => none)) ((Replacement.abstract ⟨x, ind⟩).apply e) =
      some (Pure.bind x p) := by
  have h := (reads_replace 1 (abstractAt x) (Readback.abstractAt_heads x)
    (Readback.abstractAt_lift x) scope (fun n => scope (1 + n))
    scope_succ (fun n => scope_succ (1 + n))
    (fun n => Pure.BTerm.var ∘ closeAt x n)
    (by intro n; simp only [Pure.Substitution.lift_ofRen, closeAt_lift])
    (abstract_bound x) (fun n y => abstract_free x y n)).2.1 0 _ e (by simp) p hp
  simpa [Readback.abstractAt_zero, scope_succ, Pure.BFormula.subst_ofRen,
    closeAt_zero, Pure.bind] using h

theorem term_abstract {e : Term ind} {t : BTerm 0}
    (ht : term (fun _ => none) e = some t) (x : Identifier) :
    term (Readback.bind (fun _ => none)) ((Replacement.abstract ⟨x, ind⟩).apply e) =
      some (t.rename (Pure.close x)) := by
  have h := (reads_replace 1 (abstractAt x) (Readback.abstractAt_heads x)
    (Readback.abstractAt_lift x) scope (fun n => scope (1 + n))
    scope_succ (fun n => scope_succ (1 + n))
    (fun n => Pure.BTerm.var ∘ closeAt x n)
    (by intro n; simp only [Pure.Substitution.lift_ofRen, closeAt_lift])
    (abstract_bound x) (fun n y => abstract_free x y n)).1 0 _ e (by simp) t ht
  simpa [Readback.abstractAt_zero, scope_succ, Pure.BTerm.subst_ofRen,
    closeAt_zero] using h

/-! Individual substitution commutes with readback. -/
open Pure (Renaming Substitution)

/-- Include a scope below `k` outer individual binders. -/
def weakenAt (k n : Nat) : Renaming Identifier n Identifier (k + n)
  | .inl x => .inl x
  | .inr i => .inr ⟨k + i, by omega⟩

theorem weakenAt_lift (k n : Nat) : weakenAt k (n + 1) = (weakenAt k n).lift := by
  funext z
  cases z with
  | inl x => rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [weakenAt, Pure.Renaming.lift, Pure.shift, Fin.ext_iff]

private abbrev identity : Replacement := Replacement.ofSub Sub.id

private theorem identity_heads : Readback.PreservesHeads identity where
  free _ _ _ := rfl
  const _ _ := rfl
  bound _ _ i := ⟨i, rfl⟩

private theorem identity_lift : identity.lift ind = identity := by
  simp [identity]

private theorem weaken_bound (k n i : Nat) (t : BTerm n)
    (ht : term (scope n) (.bound i) = some t) :
    term (scope (k + n)) (identity.bound ind i) =
      some (t.subst (Pure.BTerm.var ∘ weakenAt k n)) := by
  by_cases hi : i < n
  · simp only [term, scope, hi, ↓reduceDIte, Option.map_some, Option.some.injEq] at ht
    subst t
    simp [identity, Replacement.ofSub, Sub.id, term, scope, show i < k + n by omega,
      weakenAt, Pure.BTerm.subst, Fin.ext_iff]
    omega
  · simp [term, scope, hi] at ht

private theorem weaken_free (k n : Nat) (x : Identifier) (t : BTerm n)
    (ht : term (scope n) (.free x) = some t) :
    term (scope (k + n)) (identity.free ind x) =
      some (t.subst (Pure.BTerm.var ∘ weakenAt k n)) := by
  simp only [term, Option.some.injEq] at ht
  subst t
  simp [identity, Replacement.ofSub, term, Pure.BTerm.subst, weakenAt]

theorem term_closed {e : Term ind} {t : BTerm 0}
    (ht : term (fun _ => none) e = some t) (k : Nat) :
    term (scope k) e = some (t.rename (weakenAt k 0)) := by
  have h := (reads_replace k (fun _ => identity) (fun _ => identity_heads)
    (fun _ => identity_lift.symm) scope (fun n => scope (k + n))
    scope_succ (fun n => scope_succ (k + n))
    (fun n => Pure.BTerm.var ∘ weakenAt k n)
    (by intro n; simp only [Pure.Substitution.lift_ofRen, weakenAt_lift])
    (weaken_bound k) (weaken_free k)).1 0 _ e (by simp) t ht
  simpa [identity, Pure.BTerm.subst_ofRen] using h

/-- The same replacement term, with no ambient bound slots, is used at every depth. -/
def singleAt (x : Identifier) (t : BTerm 0) (n : Nat) :
    Substitution Readback.language Identifier n Identifier (0 + n)
  | .inl y => if y = x then t.rename (weakenAt (0 + n) 0) else .var (.inl y)
  | .inr i => .var (.inr ⟨i, by omega⟩)

theorem singleAt_lift (x : Identifier) (t : BTerm 0) (n : Nat) :
    singleAt x t (n + 1) = (singleAt x t n).lift := by
  have h : Pure.shift ∘ weakenAt (0 + n) 0 = weakenAt (0 + (n + 1)) 0 := by
    funext z
    cases z with
    | inl _ => rfl
    | inr i => exact i.elim0
  funext z
  cases z with
  | inl y =>
    by_cases hy : y = x <;>
      simp [singleAt, Pure.Substitution.lift, hy, Pure.BTerm.rename_comp,
        Pure.BTerm.rename, h]
    rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [singleAt, Pure.Substitution.lift, Pure.BTerm.rename, Pure.shift,
        Fin.ext_iff]

private theorem single_bound (x : Identifier) (a : Term ind) (t : BTerm 0)
    (n i : Nat) (u : BTerm n) (hu : term (scope n) (.bound i) = some u) :
    term (scope (0 + n)) ((Replacement.single ⟨x, ind⟩ a).bound ind i) =
      some (u.subst (singleAt x t n)) := by
  by_cases hi : i < n
  · simp only [term, scope, hi, ↓reduceDIte, Option.map_some, Option.some.injEq] at hu
    subst u
    simp [Replacement.single, Sub.id, term, scope, hi, Pure.BTerm.subst, singleAt]
  · simp [term, scope, hi] at hu

private theorem single_free (x : Identifier) (a : Term ind) (t : BTerm 0)
    (ht : term (fun _ => none) a = some t) (n : Nat) (y : Identifier)
    (u : BTerm n) (hu : term (scope n) (.free y) = some u) :
    term (scope (0 + n)) ((Replacement.single ⟨x, ind⟩ a).free ind y) =
      some (u.subst (singleAt x t n)) := by
  simp only [term, Option.some.injEq] at hu
  subst u
  by_cases h : y = x
  · subst y
    simpa [Replacement.single, singleAt, Pure.BTerm.subst] using term_closed ht (0 + n)
  · simp [Replacement.single, singleAt, Pure.BTerm.subst, term, h]

private theorem singleAt_zero (x : Identifier) (t : BTerm 0) : singleAt x t 0 = Pure.single x t := by
  have h : weakenAt 0 0 = id := by
    funext z
    cases z with
    | inl _ => rfl
    | inr i => exact i.elim0
  funext z
  cases z with
  | inl y => simp [singleAt, Pure.single, h]
  | inr i => exact i.elim0

theorem formula_single {e : Term prop} {p : BFormula 0}
    (hp : formula (fun _ => none) e = some p) (x : Identifier)
    {a : Term ind} {t : BTerm 0} (ht : term (fun _ => none) a = some t)
    (ha : a.shift ind = a) :
    formula (fun _ => none) ((Replacement.single ⟨x, ind⟩ a).apply e) =
      some (Pure.substOne x t p) := by
  have bridge := reads_replace 0 (fun _ => Replacement.single ⟨x, ind⟩ a)
    (fun _ => Readback.single_heads x a) (fun _ => (Readback.single_lift x a ha).symm)
    scope (fun n => scope (0 + n)) scope_succ (fun n => scope_succ (0 + n))
  have h := (bridge (singleAt x t) (singleAt_lift x t)
    (single_bound x a t) (single_free x a t ht)).2.1 0 _ e (by simp) p hp
  simpa [singleAt_zero, Pure.substOne] using h

theorem term_single {e : Term ind} {u : BTerm 0}
    (hu : term (fun _ => none) e = some u) (x : Identifier)
    {a : Term ind} {t : BTerm 0} (ht : term (fun _ => none) a = some t)
    (ha : a.shift ind = a) :
    term (fun _ => none) ((Replacement.single ⟨x, ind⟩ a).apply e) =
      some (u.subst (Pure.single x t)) := by
  have bridge := reads_replace 0 (fun _ => Replacement.single ⟨x, ind⟩ a)
    (fun _ => Readback.single_heads x a) (fun _ => (Readback.single_lift x a ha).symm)
    scope (fun n => scope (0 + n)) scope_succ (fun n => scope_succ (0 + n))
  have h := (bridge (singleAt x t) (singleAt_lift x t)
    (single_bound x a t) (single_free x a t ht)).1 0 _ e (by simp) u hu
  simpa [singleAt_zero] using h

end Lisa.SCLambdaToPure.Readback
