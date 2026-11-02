import Lisa.LambdaFol.ToPureFol.PureFolTranslation
import Lisa.LambdaFol.ToPureFol.PureFolSubstitution

/-! Reading commutes with capture-avoiding individual replacement.
The mutual reader induction covers formulas inside epsilon terms. It states
preservation of successful reads; unsupported source syntax is not required
to remain unsupported after a replacement. -/
namespace Lisa.LambdaFol.PureFolTranslation
open AlphaBetaEtaNormalization
open PureFol (BoundedTerm.subst BoundedFormula.subst Substitution)

private theorem func_subst (σ : Substitution PureFolTranslation.language Identifier n Identifier m)
    (c : Symbol) (ts : List (BoundedTerm n)) :
    (PureFol.BoundedTerm.func c ts.get).subst σ =
      .func c (ts.map (fun t => t.subst σ)).get := by
  simp only [PureFol.BoundedTerm.subst, PureFol.BoundedTerm.func.injEq]
  refine ⟨(List.length_map ..).symm, HEq.rfl, ?_⟩
  apply (Fin.heq_fun_iff (by simp)).mpr
  intro i
  simp

private theorem rel_subst (σ : Substitution PureFolTranslation.language Identifier n Identifier m)
    (c : Symbol) (ts : List (BoundedTerm n)) :
    (PureFol.BoundedFormula.rel c ts.get).subst σ =
      .rel c (ts.map (fun t => t.subst σ)).get := by
  simp only [PureFol.BoundedFormula.subst, PureFol.BoundedFormula.rel.injEq]
  refine ⟨(List.length_map ..).symm, HEq.rfl, ?_⟩
  apply (Fin.heq_fun_iff (by simp)).mpr
  intro i
  simp

private theorem apply_eq_const (R : SymbolSubstitution) (hR : PreservesHeads R)
    (hs : s ≠ ind) (e : Term s) (c : Identifier) :
    R.apply e = .const c ↔ e = .const c := by
  cases e with
  | bound i =>
      obtain ⟨j, hj⟩ := hR.bound s hs i
      simp [SymbolSubstitution.apply, hj]
  | free x => simp [SymbolSubstitution.apply, hR.free s hs]
  | const d => simp [SymbolSubstitution.apply, hR.const]
  | app | lam => simp [SymbolSubstitution.apply]

private theorem not_eq_head (R : SymbolSubstitution) (hR : PreservesHeads R)
    (e : Term (ind >> prop))
    (h : ∀ a : Term ind, e ≠ .app (.const ⟨"eq", 0⟩) a) :
    ∀ a : Term ind, R.apply e ≠ .app (.const ⟨"eq", 0⟩) a := by
  intro a ha
  cases e with
  | bound i =>
      obtain ⟨j, hj⟩ := hR.bound (ind >> prop) (by simp) i
      simp [SymbolSubstitution.apply, hj] at ha
  | free x => simp [SymbolSubstitution.apply, hR.free (ind >> prop) (by simp)] at ha
  | const d => simp [SymbolSubstitution.apply, hR.const] at ha
  | lam => simp [SymbolSubstitution.apply] at ha
  | @app s f t =>
      simp only [SymbolSubstitution.apply, Term.app.injEq] at ha
      obtain ⟨rfl, hf, _⟩ := ha
      have hf' : t = .const ⟨"eq", 0⟩ :=
        (apply_eq_const R hR (by simp) t _).mp (eq_of_heq hf)
      exact h _ (by rw [hf'])

/-- Source replacement commutes with translation to PureFol when
they agree on leaves and lift together under an individual binder. The source
has `n` surrounding individual binders and the target has `k + n`; both use the
standard index-to-level map `indexToLevel`. Application spines share the same induction. -/
theorem reads_replace (k : Nat) (R : Nat → SymbolSubstitution)
    (hR : ∀ n, PreservesHeads (R n)) (hRl : ∀ n, R (n + 1) = (R n).lift ind)
    (σ : ∀ n, Substitution PureFolTranslation.language Identifier n Identifier (k + n))
    (hσ : ∀ n, σ (n + 1) = (σ n).lift)
    (hb : ∀ n i t, fromNormalTerm? (indexToLevel n) (.bound i) = some t →
      fromNormalTerm? (indexToLevel (k + n)) ((R n).bound ind i) = some (t.subst (σ n)))
    (hv : ∀ n x t, fromNormalTerm? (indexToLevel n) (.free x) = some t →
      fromNormalTerm? (indexToLevel (k + n)) ((R n).free ind x) = some (t.subst (σ n))) :
    (∀ n r e, r = indexToLevel n → ∀ t, fromNormalTerm? r e = some t →
      fromNormalTerm? (indexToLevel (k + n)) ((R n).apply e) = some (t.subst (σ n))) ∧
    (∀ n r e, r = indexToLevel n → ∀ p, fromNormalFormula? r e = some p →
      fromNormalFormula? (indexToLevel (k + n)) ((R n).apply e) = some (p.subst (σ n))) ∧
    (∀ s n r (e : Term s), r = indexToLevel n → s ≠ ind → ∀ c ts,
      symbolAndArguments? r e = some (c, ts) →
      symbolAndArguments? (indexToLevel (k + n)) ((R n).apply e) = some (c, ts.map (fun t => t.subst (σ n)))) := by
  apply fromNormalTerm?.mutual_induct
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
    simp only [fromNormalTerm?, Option.some.injEq] at ht
    subst t
    simp only [SymbolSubstitution.apply, (hR n).const, fromNormalTerm?, PureFol.BoundedTerm.subst]
    congr 2
    funext i
    exact i.elim0
  case case4 =>
    intro n r f a ihf iha hr t ht
    rcases hf : symbolAndArguments? r f with _ | ⟨c, ts⟩ <;>
      simp [fromNormalTerm?, hf] at ht
    rcases ha : fromNormalTerm? r a with _ | u <;>
      simp [ha] at ht
    cases ht
    simp [SymbolSubstitution.apply, fromNormalTerm?, ihf hr (by simp) _ _ hf, iha hr _ ha,
      func_subst, -PureFol.BoundedTerm.func.injEq]
    apply congrArg (fun us : List (BoundedTerm (k + n)) => PureFol.BoundedTerm.func c us.get)
    simp
  case case5 =>
    intro n r p ih hr t ht
    rcases hp : fromNormalFormula? (PureFolTranslation.bind r) p with _ | q <;>
      simp [fromNormalTerm?, hp] at ht
    cases ht
    have hi := ih (by rw [hr, indexToLevel_succ]) q hp
    rw [hRl, hσ] at hi
    change fromNormalFormula? (indexToLevel ((k + n) + 1)) _ = _ at hi
    rw [indexToLevel_succ] at hi
    simp [SymbolSubstitution.apply, (hR n).const, fromNormalTerm?, hi, PureFol.BoundedTerm.subst]
  -- Unsupported term syntax.
  case case6 | case7 =>
    intros
    simp_all [fromNormalTerm?]
  -- Truth and falsehood.
  case case8 | case9 =>
    intro n r _ p hp
    simp only [fromNormalFormula?, Option.some.injEq] at hp
    subst p
    simp [SymbolSubstitution.apply, (hR n).const, fromNormalFormula?, PureFol.BoundedFormula.subst]
  case case10 =>
    intro n r p ih hr q hq
    cases hp : fromNormalFormula? r p <;> simp [fromNormalFormula?, hp] at hq
    subst q
    simp [SymbolSubstitution.apply, (hR n).const, fromNormalFormula?, ih hr _ hp, PureFol.BoundedFormula.subst]
  -- All four binary propositional connectives use the same argument.
  case case11 | case12 | case13 | case14 =>
    intro n r p q ihp ihq hr u hu
    cases hp : fromNormalFormula? r p <;> simp [fromNormalFormula?, hp] at hu
    cases hq : fromNormalFormula? r q <;> simp [hq] at hu
    subst u
    simp [SymbolSubstitution.apply, (hR n).const, fromNormalFormula?, ihp hr _ hp, ihq hr _ hq, PureFol.BoundedFormula.subst]
  case case15 =>
    intro n r t u iht ihu hr p hp
    cases ht : fromNormalTerm? r t <;> simp [fromNormalFormula?, ht] at hp
    cases hu : fromNormalTerm? r u <;> simp [hu] at hp
    subst p
    simp [SymbolSubstitution.apply, (hR n).const, fromNormalFormula?, iht hr _ ht, ihu hr _ hu, PureFol.BoundedFormula.subst]
  -- Universal and existential quantification.
  case case16 | case17 =>
    intro n r p ih hr q hq
    cases hp : fromNormalFormula? (PureFolTranslation.bind r) p <;> simp [fromNormalFormula?, hp] at hq
    subst q
    have hi := ih (by rw [hr, indexToLevel_succ]) _ hp
    rw [hRl, hσ] at hi
    change fromNormalFormula? (indexToLevel ((k + n) + 1)) _ = _ at hi
    rw [indexToLevel_succ] at hi
    simp [SymbolSubstitution.apply, (hR n).const, fromNormalFormula?, hi, PureFol.BoundedFormula.subst]
  case case18 =>
    intro n r x _ p hp
    simp only [fromNormalFormula?, Option.some.injEq] at hp
    subst p
    simp only [SymbolSubstitution.apply, (hR n).free prop (by decide), fromNormalFormula?, PureFol.BoundedFormula.subst]
    congr 2
    funext i
    exact i.elim0
  case case19 =>
    intro n r c ht hb _ p hp
    simp [fromNormalFormula?] at hp
    subst p
    simp only [SymbolSubstitution.apply, (hR n).const, fromNormalFormula?, PureFol.BoundedFormula.subst]
    congr 2
    funext i
    exact i.elim0
  case case20 =>
    intro n r f a h ihf iha hr p hp
    have h' := not_eq_head (R n) (hR n) f h
    rcases hf : symbolAndArguments? r f with _ | ⟨c, ts⟩ <;>
      simp [fromNormalFormula?, hf] at hp
    rcases ha : fromNormalTerm? r a with _ | t <;>
      simp [ha] at hp
    subst p
    simp [SymbolSubstitution.apply, fromNormalFormula?, ihf hr (by simp) _ _ hf, iha hr _ ha,
      rel_subst, -PureFol.BoundedFormula.rel.injEq]
    apply congrArg (fun us : List (BoundedTerm (k + n)) => PureFol.BoundedFormula.rel c us.get)
    simp
  case case21 =>
    intros
    simp_all [fromNormalFormula?]
  case case22 =>
    intro s n r x _ hs c ts h
    simp only [symbolAndArguments?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [SymbolSubstitution.apply, (hR n).free s hs, symbolAndArguments?]
  case case23 =>
    intro s n r x _ _ c ts h
    simp only [symbolAndArguments?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [SymbolSubstitution.apply, (hR n).const, symbolAndArguments?]
  case case24 =>
    intro s n r f a ihf iha hr _ c ts h
    rcases hf : symbolAndArguments? r f with _ | ⟨d, us⟩ <;>
      simp [symbolAndArguments?, hf] at h
    rcases ha : fromNormalTerm? r a with _ | t <;>
      simp [ha] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [SymbolSubstitution.apply, symbolAndArguments?, ihf hr (by simp) _ _ hf, iha hr _ ha]
  case case25 =>
    intros
    simp_all [symbolAndArguments?]

end Lisa.LambdaFol.PureFolTranslation

/-! Translation to PureFol commutes with abstraction of a free individual name and substitution
of an individual term. Both operations preserve inner quantifier and epsilon binders. -/
namespace Lisa.LambdaFol.PureFolTranslation
open AlphaBetaEtaNormalization
open PureFol (Renaming)

def closeAt (x : Identifier) (n : Nat) : Renaming Identifier n Identifier (1 + n)
  | .inl y => if y = x then .inr ⟨0, by omega⟩ else .inl y
  | .inr i => .inr ⟨i + 1, by omega⟩

theorem closeAt_lift (x : Identifier) (n : Nat) : closeAt x (n + 1) = (closeAt x n).lift := by
  funext z
  cases z with
  | inl y =>
    by_cases h : y = x <;> simp [closeAt, PureFol.Renaming.lift, PureFol.shift, h]
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [closeAt, PureFol.Renaming.lift, PureFol.shift, Fin.ext_iff, Nat.add_comm]

private theorem abstract_bound (x : Identifier) (n i : Nat) (t : BoundedTerm n)
    (ht : fromNormalTerm? (indexToLevel n) (.bound i) = some t) :
    fromNormalTerm? (indexToLevel (1 + n)) ((abstractAt x n).bound ind i) =
      some (t.subst (PureFol.BoundedTerm.var ∘ closeAt x n)) := by
  by_cases hi : i < n
  · simp only [fromNormalTerm?, indexToLevel, hi, ↓reduceDIte, Option.map_some, Option.some.injEq] at ht
    subst t
    simp [abstractAt, show ¬n ≤ i by omega, fromNormalTerm?, indexToLevel,
      show i < 1 + n by omega, closeAt, PureFol.BoundedTerm.subst, Fin.ext_iff]
    omega
  · simp [fromNormalTerm?, indexToLevel, hi] at ht

private theorem abstract_free (x y : Identifier) (n : Nat) (t : BoundedTerm n)
    (ht : fromNormalTerm? (indexToLevel n) (.free y) = some t) :
    fromNormalTerm? (indexToLevel (1 + n)) ((abstractAt x n).free ind y) =
      some (t.subst (PureFol.BoundedTerm.var ∘ closeAt x n)) := by
  simp only [fromNormalTerm?, Option.some.injEq] at ht
  subst t
  by_cases h : y = x
  · subst y
    simp [abstractAt, fromNormalTerm?, indexToLevel, closeAt, PureFol.BoundedTerm.subst]
  · simp [abstractAt, h, fromNormalTerm?, closeAt, PureFol.BoundedTerm.subst]

private theorem closeAt_zero (x : Identifier) : closeAt x 0 = PureFol.close x := by
  funext z
  cases z with
  | inl y => rfl
  | inr i => exact i.elim0

theorem fromNormalFormula_abstract {e : Term prop} {p : BoundedFormula 0}
    (hp : fromNormalFormula? (fun _ => none) e = some p) (x : Identifier) :
    fromNormalFormula? (PureFolTranslation.bind (fun _ => none)) ((SymbolSubstitution.abstract ⟨x, ind⟩).apply e) =
      some (PureFol.bind x p) := by
  have h := (reads_replace 1 (abstractAt x) (PureFolTranslation.abstractAt_heads x)
    (PureFolTranslation.abstractAt_lift x)
    (fun n => PureFol.BoundedTerm.var ∘ closeAt x n)
    (by intro n; simp only [PureFol.Substitution.lift_ofRen, closeAt_lift])
    (abstract_bound x) (fun n y => abstract_free x y n)).2.1 0 _ e (by simp) p hp
  simpa [PureFolTranslation.abstractAt_zero, indexToLevel_succ, PureFol.BoundedFormula.subst_ofRen,
    closeAt_zero, PureFol.bind] using h

/-! Individual substitution commutes with translation to PureFol. -/
open PureFol (Renaming Substitution)

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
      simp [weakenAt, PureFol.Renaming.lift, PureFol.shift, Fin.ext_iff]

private abbrev identity : SymbolSubstitution := SymbolSubstitution.ofSub Sub.id

private theorem identity_heads : PureFolTranslation.PreservesHeads identity where
  free _ _ _ := rfl
  const _ _ := rfl
  bound _ _ i := ⟨i, rfl⟩

private theorem identity_lift : identity.lift ind = identity := by
  simp [identity]

private theorem weaken_bound (k n i : Nat) (t : BoundedTerm n)
    (ht : fromNormalTerm? (indexToLevel n) (.bound i) = some t) :
    fromNormalTerm? (indexToLevel (k + n)) (identity.bound ind i) =
      some (t.subst (PureFol.BoundedTerm.var ∘ weakenAt k n)) := by
  by_cases hi : i < n
  · simp only [fromNormalTerm?, indexToLevel, hi, ↓reduceDIte, Option.map_some, Option.some.injEq] at ht
    subst t
    simp [identity, SymbolSubstitution.ofSub, Sub.id, fromNormalTerm?, indexToLevel, show i < k + n by omega,
      weakenAt, PureFol.BoundedTerm.subst, Fin.ext_iff]
    omega
  · simp [fromNormalTerm?, indexToLevel, hi] at ht

private theorem weaken_free (k n : Nat) (x : Identifier) (t : BoundedTerm n)
    (ht : fromNormalTerm? (indexToLevel n) (.free x) = some t) :
    fromNormalTerm? (indexToLevel (k + n)) (identity.free ind x) =
      some (t.subst (PureFol.BoundedTerm.var ∘ weakenAt k n)) := by
  simp only [fromNormalTerm?, Option.some.injEq] at ht
  subst t
  simp [identity, SymbolSubstitution.ofSub, fromNormalTerm?, PureFol.BoundedTerm.subst, weakenAt]

theorem fromNormalTerm_locallyClosed {e : Term ind} {t : BoundedTerm 0}
    (ht : fromNormalTerm? (fun _ => none) e = some t) (k : Nat) :
    fromNormalTerm? (indexToLevel k) e = some (t.rename (weakenAt k 0)) := by
  have h := (reads_replace k (fun _ => identity) (fun _ => identity_heads)
    (fun _ => identity_lift.symm)
    (fun n => PureFol.BoundedTerm.var ∘ weakenAt k n)
    (by intro n; simp only [PureFol.Substitution.lift_ofRen, weakenAt_lift])
    (weaken_bound k) (weaken_free k)).1 0 _ e (by simp) t ht
  simpa [identity, PureFol.BoundedTerm.subst_ofRen] using h

/-- The same replacement term, with no ambient bound slots, is used at every depth. -/
def singleAt (x : Identifier) (t : BoundedTerm 0) (n : Nat) :
    Substitution PureFolTranslation.language Identifier n Identifier (0 + n)
  | .inl y => if y = x then t.rename (weakenAt (0 + n) 0) else .var (.inl y)
  | .inr i => .var (.inr ⟨i, by omega⟩)

theorem singleAt_lift (x : Identifier) (t : BoundedTerm 0) (n : Nat) :
    singleAt x t (n + 1) = (singleAt x t n).lift := by
  have h : PureFol.shift ∘ weakenAt (0 + n) 0 = weakenAt (0 + (n + 1)) 0 := by
    funext z
    cases z with
    | inl _ => rfl
    | inr i => exact i.elim0
  funext z
  cases z with
  | inl y =>
    by_cases hy : y = x <;>
      simp [singleAt, PureFol.Substitution.lift, hy, PureFol.BoundedTerm.rename_comp,
        PureFol.BoundedTerm.rename, h]
    rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [singleAt, PureFol.Substitution.lift, PureFol.BoundedTerm.rename, PureFol.shift,
        Fin.ext_iff]

private theorem single_bound (x : Identifier) (a : Term ind) (t : BoundedTerm 0)
    (n i : Nat) (u : BoundedTerm n) (hu : fromNormalTerm? (indexToLevel n) (.bound i) = some u) :
    fromNormalTerm? (indexToLevel (0 + n)) ((SymbolSubstitution.single ⟨x, ind⟩ a).bound ind i) =
      some (u.subst (singleAt x t n)) := by
  by_cases hi : i < n
  · simp only [fromNormalTerm?, indexToLevel, hi, ↓reduceDIte, Option.map_some, Option.some.injEq] at hu
    subst u
    simp [SymbolSubstitution.single, Sub.id, fromNormalTerm?, indexToLevel, hi, PureFol.BoundedTerm.subst, singleAt]
  · simp [fromNormalTerm?, indexToLevel, hi] at hu

private theorem single_free (x : Identifier) (a : Term ind) (t : BoundedTerm 0)
    (ht : fromNormalTerm? (fun _ => none) a = some t) (n : Nat) (y : Identifier)
    (u : BoundedTerm n) (hu : fromNormalTerm? (indexToLevel n) (.free y) = some u) :
    fromNormalTerm? (indexToLevel (0 + n)) ((SymbolSubstitution.single ⟨x, ind⟩ a).free ind y) =
      some (u.subst (singleAt x t n)) := by
  simp only [fromNormalTerm?, Option.some.injEq] at hu
  subst u
  by_cases h : y = x
  · subst y
    simpa [SymbolSubstitution.single, singleAt, PureFol.BoundedTerm.subst] using fromNormalTerm_locallyClosed ht (0 + n)
  · simp [SymbolSubstitution.single, singleAt, PureFol.BoundedTerm.subst, fromNormalTerm?, h]

private theorem singleAt_zero (x : Identifier) (t : BoundedTerm 0) : singleAt x t 0 = PureFol.single x t := by
  have h : weakenAt 0 0 = id := by
    funext z
    cases z with
    | inl _ => rfl
    | inr i => exact i.elim0
  funext z
  cases z with
  | inl y => simp [singleAt, PureFol.single, h]
  | inr i => exact i.elim0

theorem fromNormalFormula_single {e : Term prop} {p : BoundedFormula 0}
    (hp : fromNormalFormula? (fun _ => none) e = some p) (x : Identifier)
    {a : Term ind} {t : BoundedTerm 0} (ht : fromNormalTerm? (fun _ => none) a = some t)
    (ha : a.shift ind = a) :
    fromNormalFormula? (fun _ => none) ((SymbolSubstitution.single ⟨x, ind⟩ a).apply e) =
      some (PureFol.substOne x t p) := by
  have bridge := reads_replace 0 (fun _ => SymbolSubstitution.single ⟨x, ind⟩ a)
    (fun _ => PureFolTranslation.single_heads x a) (fun _ => (PureFolTranslation.single_lift x a ha).symm)
  have h := (bridge (singleAt x t) (singleAt_lift x t)
    (single_bound x a t) (single_free x a t ht)).2.1 0 _ e (by simp) p hp
  simpa [singleAt_zero, PureFol.substOne] using h

theorem fromNormalTerm_single {e : Term ind} {u : BoundedTerm 0}
    (hu : fromNormalTerm? (fun _ => none) e = some u) (x : Identifier)
    {a : Term ind} {t : BoundedTerm 0} (ht : fromNormalTerm? (fun _ => none) a = some t)
    (ha : a.shift ind = a) :
    fromNormalTerm? (fun _ => none) ((SymbolSubstitution.single ⟨x, ind⟩ a).apply e) =
      some (u.subst (PureFol.single x t)) := by
  have bridge := reads_replace 0 (fun _ => SymbolSubstitution.single ⟨x, ind⟩ a)
    (fun _ => PureFolTranslation.single_heads x a) (fun _ => (PureFolTranslation.single_lift x a ha).symm)
  have h := (bridge (singleAt x t) (singleAt_lift x t)
    (single_bound x a t) (single_free x a t ht)).1 0 _ e (by simp) u hu
  simpa [singleAt_zero] using h

end Lisa.LambdaFol.PureFolTranslation
