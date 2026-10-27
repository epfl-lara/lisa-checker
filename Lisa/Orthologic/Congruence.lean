import Lisa.Orthologic.Derivation

/-! Equality at arbitrary simple sorts, expressed by replacement in formulas.
Every obligation in this file is a derivation in `Ordered AlphaBetaEta`.
-/

namespace Lisa.Orthologic
open Expr Derivation Ordered

/-- Two expressions are interchangeable in every well-sorted formula context. -/
def ContextEq (s : LSort) (p q : Expr) : Prop :=
  ∀ k, k.hasSort (s >> prop) →
    Nonempty (Entails (.app k p) (.app k q)) ∧ Nonempty (Entails (.app k q) (.app k p))

namespace ContextEq

variable {s t : LSort} {k p q r : Expr}

theorem app_sort (hk : k.hasSort (s >> t)) (hp : p.hasSort s) :
    (Expr.app k p).hasSort t := by
  change k.sort = some (s >> t) at hk
  change p.sort = some s at hp
  simp [hasSort, Expr.sort, hk, hp]

theorem refl (hp : p.hasSort s) : ContextEq s p p := by
  intro k hk
  exact ⟨⟨.hypothesis _ (app_sort hk hp)⟩, ⟨.hypothesis _ (app_sort hk hp)⟩⟩

theorem symm (h : ContextEq s p q) : ContextEq s q p := fun k hk => (h k hk).symm

theorem trans (hp : p.hasSort s) (hq : q.hasSort s) (hr : r.hasSort s)
    (h : ContextEq s p q) (j : ContextEq s q r) : ContextEq s p r := by
  intro k hk
  obtain ⟨⟨hpq⟩, ⟨hqp⟩⟩ := h k hk
  obtain ⟨⟨hqr⟩, ⟨hrq⟩⟩ := j k hk
  exact ⟨⟨Derivation.trans (app_sort hk hp) (app_sort hk hq) (app_sort hk hr) hpq hqr⟩,
    ⟨Derivation.trans (app_sort hk hr) (app_sort hk hq) (app_sort hk hp) hrq hqp⟩⟩

theorem of_conversion (hp : p.hasSort s) (h : AlphaBetaEta p q) : ContextEq s p q := by
  intro k hk
  have hq : q.hasSort s := h.preserves_sort.symm.trans hp
  exact ⟨⟨convert (app_sort hk hp) (app_sort hk hp) (.refl _) (.app (.refl _) h)
      (.hypothesis _ (app_sort hk hp))⟩,
    ⟨convert (app_sort hk hq) (app_sort hk hq) (.refl _) (.app (.refl _) h.symm)
      (.hypothesis _ (app_sort hk hq))⟩⟩

theorem of_pointwise (hp : p.hasSort s) (xs : List SVar)
    (hv : (SubstPair.mk p q).validParams xs)
    (d : Nonempty (Theorem ((SubstPair.mk p q).pointwiseEq xs))) : ContextEq s p q := by
  intro k hk
  obtain ⟨d⟩ := d
  let z := Lambda.Context.empty.fresh k.freeVars s
  have hz := Lambda.Context.empty.fresh_not_mem k.freeVars s
  have hbody : isFormula (.app k (.var z)) := app_sort hk rfl
  have valid := replacement_valid (z := z) (xs := xs) hbody hp hv
  have forward := replace (replacement z (.app k (.var z)) p q xs) valid d
  have backward := replace_reverse (replacement z (.app k (.var z)) p q xs) valid d
  have hc (e : Expr) : AlphaBetaEta (substOne z e (.app k (.var z))) (.app k e) := by
    simpa [substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (substOne_fresh hk z e hz) (.refl e)
  exact ⟨⟨convert valid.2.2.2.1 valid.2.2.2.2 (hc p) (hc q) forward⟩,
    ⟨convert valid.2.2.2.2 valid.2.2.2.1 (hc q) (hc p) backward⟩⟩

theorem of_formula (hp : isFormula p) (hq : isFormula q)
    (d : Nonempty (Entails p q)) (e : Nonempty (Entails q p)) : ContextEq prop p q := by
  obtain ⟨d⟩ := d
  obtain ⟨e⟩ := e
  have valid : (SubstPair.mk p q).validParams [] := by
    simp [SubstPair.validParams, SubstPair.wellSorted, SubstPair.sort, Expr.wellSorted,
      show p.sort = some prop from hp, show q.sort = some prop from hq, LSort.splitArgs]
  apply of_pointwise hp [] valid
  simpa [SubstPair.pointwiseEq, SubstPair.sort, show p.sort = some prop from hp,
    LSort.splitArgs, Expr.applied] using Nonempty.intro (iff_intro hp hq d e)

theorem formula (hp : isFormula p) (hq : isFormula q) (h : ContextEq prop p q) :
    Nonempty (Entails p q) ∧ Nonempty (Entails q p) := by
  let x : SVar := ⟨⟨"identity", 0⟩, prop⟩
  let k : Expr := .lam x (.var x)
  have hk : k.hasSort (prop >> prop) := rfl
  have beta (e : Expr) (he : isFormula e) : AlphaBetaEta (.app k e) e := by
    simpa [substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.beta x (.var x) e he
  obtain ⟨⟨d⟩, ⟨e⟩⟩ := h k hk
  exact ⟨⟨convert (app_sort hk hp) (app_sort hk hq) (beta p hp) (beta q hq) d⟩,
    ⟨convert (app_sort hk hq) (app_sort hk hp) (beta q hq) (beta p hp) e⟩⟩

/-- Choose independent variables, avoiding the complete supplied finite support. -/
def freshArgs : List LSort → Finset SVar → List SVar
  | [], _ => []
  | s :: ss, avoid =>
      let x := Lambda.Context.empty.fresh avoid s
      x :: freshArgs ss (insert x avoid)

theorem freshArgs_properties (ss : List LSort) (avoid : Finset SVar) :
    (freshArgs ss avoid).map SVar.sort = ss ∧ (freshArgs ss avoid).Nodup ∧
      ∀ x ∈ freshArgs ss avoid, x ∉ avoid := by
  induction ss generalizing avoid with
  | nil => simp [freshArgs]
  | cons s ss ih =>
      let x := Lambda.Context.empty.fresh avoid s
      obtain ⟨hs, hn, hf⟩ := ih (insert x avoid)
      have hx := Lambda.Context.empty.fresh_not_mem avoid s
      refine ⟨by simpa [freshArgs, x] using congrArg (List.cons s) hs, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨fun h => hf x h (Finset.mem_insert_self _ _), hn⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact fun h => hf y hy (Finset.mem_insert_of_mem h)

theorem freshArgs_valid (hp : p.hasSort s) (hq : q.hasSort s) (avoid : Finset SVar) :
    (SubstPair.mk p q).validParams
      (freshArgs s.splitArgs.1 (p.freeVars ∪ q.freeVars ∪ avoid)) := by
  obtain ⟨hs, hn, hf⟩ := freshArgs_properties s.splitArgs.1 (p.freeVars ∪ q.freeVars ∪ avoid)
  exact ⟨⟨by simp [Expr.wellSorted, show p.sort = some s from hp], hp.trans hq.symm⟩,
    by simpa [SubstPair.sort, show p.sort = some s from hp] using hs, hn,
    fun x hx hm => hf x hx (Finset.mem_union_left _ hm)⟩

theorem substitute (hp : p.hasSort z.sort) (hq : q.hasSort z.sort)
    (h : ContextEq z.sort p q) (hb : isFormula body) :
    Nonempty (Entails (substOne z p body) (substOne z q body)) ∧
    Nonempty (Entails (substOne z q body) (substOne z p body)) := by
  have hk : (Expr.lam z body).hasSort (z.sort >> prop) := by
    simp [hasSort, Expr.sort, show body.sort = some prop from hb]
  obtain ⟨⟨d⟩, ⟨e⟩⟩ := h (.lam z body) hk
  exact ⟨⟨convert (app_sort hk hp) (app_sort hk hq)
      (.beta z body p hp) (.beta z body q hq) d⟩,
    ⟨convert (app_sort hk hq) (app_sort hk hp)
      (.beta z body q hq) (.beta z body p hp) e⟩⟩

theorem app_left {f g a : Expr} (hf : f.hasSort (s >> t)) (hg : g.hasSort (s >> t))
    (ha : a.hasSort s) (h : ContextEq (s >> t) f g) :
    ContextEq t (.app f a) (.app g a) := by
  intro k hk
  let z := Lambda.Context.empty.fresh (k.freeVars ∪ a.freeVars) (s >> t)
  have hz := Lambda.Context.empty.fresh_not_mem (k.freeVars ∪ a.freeVars) (s >> t)
  have hb : isFormula (.app k (.app (.var z) a)) := app_sort hk (app_sort rfl ha)
  obtain ⟨⟨d⟩, ⟨e⟩⟩ := substitute (z := z) hf hg h hb
  have cv (f : Expr) : AlphaBetaEta
      (substOne z f (.app k (.app (.var z) a))) (.app k (.app f a)) := by
    simpa [substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (substOne_fresh hk z f (fun hm => hz (Finset.mem_union_left _ hm)))
        (.app (.refl f) (substOne_fresh ha z f (fun hm => hz (Finset.mem_union_right _ hm))))
  have hs (f : Expr) (hf : f.hasSort (s >> t)) :
      isFormula (substOne z f (.app k (.app (.var z) a))) :=
    (cv f).preserves_sort.trans (app_sort hk (app_sort hf ha))
  exact ⟨⟨convert (hs f hf) (hs g hg) (cv f) (cv g) d⟩,
    ⟨convert (hs g hg) (hs f hf) (cv g) (cv f) e⟩⟩

theorem app_right {f a b : Expr} (hf : f.hasSort (s >> t))
    (ha : a.hasSort s) (hb : b.hasSort s) (h : ContextEq s a b) :
    ContextEq t (.app f a) (.app f b) := by
  intro k hk
  let z := Lambda.Context.empty.fresh (k.freeVars ∪ f.freeVars) s
  have hz := Lambda.Context.empty.fresh_not_mem (k.freeVars ∪ f.freeVars) s
  have hc : isFormula (.app k (.app f (.var z))) := app_sort hk (app_sort hf rfl)
  obtain ⟨⟨d⟩, ⟨e⟩⟩ := substitute (z := z) ha hb h hc
  have cv (a : Expr) : AlphaBetaEta
      (substOne z a (.app k (.app f (.var z)))) (.app k (.app f a)) := by
    simpa [substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (substOne_fresh hk z a (fun hm => hz (Finset.mem_union_left _ hm)))
        (.app (substOne_fresh hf z a (fun hm => hz (Finset.mem_union_right _ hm))) (.refl a))
  have hs (a : Expr) (ha : a.hasSort s) :
      isFormula (substOne z a (.app k (.app f (.var z)))) :=
    (cv a).preserves_sort.trans (app_sort hk (app_sort hf ha))
  exact ⟨⟨convert (hs a ha) (hs b hb) (cv a) (cv b) d⟩,
    ⟨convert (hs b hb) (hs a ha) (cv b) (cv a) e⟩⟩

theorem app {f g a b : Expr} (hf : f.hasSort (s >> t)) (hg : g.hasSort (s >> t))
    (ha : a.hasSort s) (hb : b.hasSort s)
    (h : ContextEq (s >> t) f g) (j : ContextEq s a b) :
    ContextEq t (.app f a) (.app g b) :=
  trans (app_sort hf ha) (app_sort hg ha) (app_sort hg hb)
    (app_left hf hg ha h) (app_right hg ha hb j)

theorem applied (hp : p.hasSort s) (hq : q.hasSort s) (h : ContextEq s p q)
    (xs : List SVar) (hx : xs.map SVar.sort = s.splitArgs.1) :
    ContextEq s.splitArgs.2 (p.applied (xs.map Expr.var)) (q.applied (xs.map Expr.var)) := by
  induction s generalizing p q xs with
  | ind => have : xs = [] := by simpa [LSort.splitArgs] using hx
           subst xs; exact h
  | prop => have : xs = [] := by simpa [LSort.splitArgs] using hx
            subst xs; exact h
  | arrow s t _ ih =>
      cases xs with
      | nil => simp [LSort.splitArgs] at hx
      | cons x xs =>
          simp only [List.map_cons, LSort.splitArgs, List.cons.injEq] at hx
          have hv : (Expr.var x).hasSort s := congrArg some hx.1
          exact ih (app_sort hp hv) (app_sort hq hv) (app_left hp hq hv h) xs hx.2

theorem individual (hp : isTerm p) (hq : isTerm q) (h : ContextEq ind p q) :
    Nonempty (Theorem (eq p q)) := by
  let z := Lambda.Context.empty.fresh p.freeVars ind
  have hz := Lambda.Context.empty.fresh_not_mem p.freeVars ind
  have hb : isFormula (eq p (.var z)) := isFormula_eq hp rfl
  obtain ⟨⟨d⟩, _⟩ := substitute (z := z) hp hq h hb
  have cv (a : Expr) : AlphaBetaEta (substOne z a (eq p (.var z))) (eq p a) := by
    simpa [eq, substOne, Expr.subst, Subst.subst, Lambda.NamedSubst.lookup_insert] using
      AlphaBetaEta.app (.app (.refl _) (substOne_fresh hp z a hz)) (.refl a)
  have d' := convert ((cv p).preserves_sort.trans (isFormula_eq hp hp))
    ((cv q).preserves_sort.trans (isFormula_eq hp hq)) (cv p) (cv q) d
  exact ⟨modusPonens (isFormula_eq hp hp) (isFormula_eq hp hq) (.rightRefl p hp) d'⟩

theorem pointwise (hp : p.hasSort s) (hq : q.hasSort s) (h : ContextEq s p q)
    (xs : List SVar) (hx : xs.map SVar.sort = s.splitArgs.1) :
    Nonempty (Theorem ((SubstPair.mk p q).pointwiseEq xs)) := by
  have hp' := SubstPair.applied_splitArgs_sort s hp xs hx
  have hq' := SubstPair.applied_splitArgs_sort s hq xs hx
  have ha := applied hp hq h xs hx
  rcases SubstPair.splitArgs_ground s with hs | hs
  · rw [hs] at hp' hq' ha
    simpa [SubstPair.pointwiseEq, SubstPair.sort, show p.sort = some s from hp, hs] using
      individual hp' hq' ha
  · rw [hs] at hp' hq' ha
    obtain ⟨⟨d⟩, ⟨e⟩⟩ := formula hp' hq' ha
    simpa [SubstPair.pointwiseEq, SubstPair.sort, show p.sort = some s from hp, hs] using
      Nonempty.intro (iff_intro hp' hq' d e)

theorem lam (x : SVar) (hp : p.hasSort s) (hq : q.hasSort s) (h : ContextEq s p q) :
    ContextEq (x.sort >> s) (.lam x p) (.lam x q) := by
  let avoid := p.freeVars ∪ q.freeVars ∪ {x}
  let xs := freshArgs s.splitArgs.1 avoid
  obtain ⟨hxs, hn, hf⟩ := freshArgs_properties s.splitArgs.1 avoid
  have hpl : (Expr.lam x p).hasSort (x.sort >> s) := by
    simp [hasSort, Expr.sort, show p.sort = some s from hp]
  have hql : (Expr.lam x q).hasSort (x.sort >> s) := by
    simp [hasSort, Expr.sort, show q.sort = some s from hq]
  have hv : (SubstPair.mk p q).validParams xs := freshArgs_valid hp hq {x}
  have hvl : (SubstPair.mk (.lam x p) (.lam x q)).validParams (x :: xs) := by
    refine ⟨⟨by simp [Expr.wellSorted, show p.sort = some s from hp],
      hpl.trans hql.symm⟩, ?_, ?_, ?_⟩
    · simpa [SubstPair.sort, show p.sort = some s from hp,
        LSort.splitArgs] using congrArg (List.cons x.sort) hxs
    · exact List.nodup_cons.mpr ⟨fun hm => hf x hm (by simp [avoid]), hn⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simp [Expr.freeVars]
      · intro hm
        apply hf y hy
        simp only [Expr.freeVars, Finset.mem_union, Finset.mem_sdiff,
          Finset.mem_singleton] at hm
        exact Finset.mem_union_left _ (hm.elim (fun h => Finset.mem_union_left _ h.1)
          (fun h => Finset.mem_union_right _ h.1))
  obtain ⟨d⟩ := pointwise hp hq h xs hxs
  exact of_pointwise hpl (x :: xs) hvl ⟨lam_pointwise x p q s xs hp hv d⟩

end ContextEq
end Lisa.Orthologic
