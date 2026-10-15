import Lisa.Lambda.NamedReflection

namespace Lisa.Lambda

/-- Compare original named expressions, reserving failure for malformed syntax. -/
def compareNamed (p q : Expr) : Option Bool :=
  compareNameless [] (p.toNameless []) (q.toNameless [])

/-- Accept exactly the well-sorted conversions of the original named calculus. -/
theorem compareNamed_true {p q : Expr} :
    compareNamed p q = some true ↔ Conversion p q ∧ p.wellSorted := by
  constructor
  · intro h
    obtain ⟨s, e, f, hp, hq, he⟩ := (compareNameless_true _ _ _).mp h
    exact ⟨conversion_of_compareNameless h, by
      have hs := (elaborate_named_sort p []).symm
      simp [hp] at hs
      simp [Expr.wellSorted, hs]⟩
  · rintro ⟨h, hp⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp
    exact compareNameless_of_conversion h hs

theorem compareNamed_none (p q : Expr) :
    compareNamed p q = none ↔ p.sort = none ∨ q.sort = none := by
  rw [compareNamed, compareNameless_none]
  exact or_congr (by simpa using elaborate_named_none p [])
    (by simpa using elaborate_named_none q [])

theorem compareNamed_false {p q : Expr} :
    compareNamed p q = some false ↔ p.wellSorted ∧ q.wellSorted ∧ ¬ Conversion p q := by
  constructor
  · intro h
    have hn : compareNamed p q ≠ none := by simp [h]
    have hn' : ¬ (p.sort = none ∨ q.sort = none) :=
      fun h => hn ((compareNamed_none p q).mpr h)
    have hp : p.wellSorted := Option.isSome_iff_ne_none.mpr (not_or.mp hn').1
    have hq : q.wellSorted := Option.isSome_iff_ne_none.mpr (not_or.mp hn').2
    exact ⟨hp, hq, fun hc => by simpa [h] using compareNamed_true.mpr ⟨hc, hp⟩⟩
  · rintro ⟨hp, hq, hc⟩
    cases h : compareNamed p q with
    | none =>
        rcases (compareNamed_none p q).mp h with h | h <;>
          simp_all [Expr.wellSorted]
    | some b =>
        cases b with
        | false => rfl
        | true => exact False.elim (hc (compareNamed_true.mp h).1)

/-- Restrict executable conversion decisions to the well-sorted fragment. -/
abbrev SortedExpr (s : LSort) := { e : Expr // e.hasSort s }

def SortedExpr.Equivalent (p q : SortedExpr s) : Prop := Conversion p.val q.val

instance : DecidableRel (SortedExpr.Equivalent (s := s)) := fun p q =>
  if h : compareNamed p q = some true then isTrue (compareNamed_true.mp h).1
  else isFalse fun hc => h (compareNameless_of_conversion hc p.property)

/-- Normalize named syntax totally, using deterministic fresh binders for the readback. -/
def normalizeNamed (p : Expr) : Option Expr :=
  (interpretNamed p Names.free).map fun ⟨_, e⟩ => (normalize e).reify Context.empty

/-- Preserve the name-erasure pipeline exactly, including malformed-input failures. -/
theorem normalizeNamed_eq (p : Expr) :
    normalizeNamed p =
      (elaborate [] (p.toNameless [])).map
        (fun ⟨_, e⟩ => (normalize e).reify Context.empty) := by
  simp only [normalizeNamed, interpretNamed_free]

/-- Certify every returned named normal form in the original conversion relation. -/
theorem normalizeNamed_sound {p q : Expr} (h : normalizeNamed p = some q) : Conversion p q := by
  cases he : elaborate [] (p.toNameless []) with
  | none => simp [normalizeNamed, interpretNamed_free, he] at h
  | some w =>
      rcases w with ⟨s, e⟩
      simp only [normalizeNamed, interpretNamed_free, he, Option.map_some, Option.some.injEq] at h
      subst q
      exact (Conversion.alpha (alpha_reify_of_elaborate he)).trans
        ((normalize_sound e).reify Context.empty)

theorem normalizeNamed_sort {p q : Expr} (h : normalizeNamed p = some q) : p.sort = q.sort :=
  (normalizeNamed_sound h).preserves_sort

theorem normalizeNamed_none (p : Expr) : normalizeNamed p = none ↔ p.sort = none := by
  rw [normalizeNamed, interpretNamed_free, Option.map_eq_none_iff]
  simpa using elaborate_named_none p []

@[simp] theorem normalizeNamed_reify (e : Term [] s) :
    normalizeNamed (e.reify Context.empty) = some ((normalize e).reify Context.empty) := by
  simp [normalizeNamed, interpretNamed_free]

/-- Preserve the result when normalizing an already normalized named expression. -/
theorem normalizeNamed_idempotent {p q : Expr} (h : normalizeNamed p = some q) :
    normalizeNamed q = some q := by
  cases he : elaborate [] (p.toNameless []) with
  | none => simp [normalizeNamed, interpretNamed_free, he] at h
  | some w =>
      rcases w with ⟨s, e⟩
      simp only [normalizeNamed, interpretNamed_free, he, Option.map_some, Option.some.injEq] at h
      subst q
      simp [normalize_idempotent]

/-- Identify well-sorted named conversions by literal equality of named normal forms. -/
theorem conversion_iff_normalizeNamed_eq {p q : Expr} (hp : p.hasSort s) :
    Conversion p q ↔ normalizeNamed p = normalizeNamed q := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := elaborate_named hp []
    obtain ⟨f, hf⟩ := elaborate_named (h.preserves_sort.symm.trans hp) []
    simp only [List.map_nil] at he hf
    have hc := elaborate_conversion h
    rw [he, hf] at hc
    cases hc with
    | some hc => simp [normalizeNamed, interpretNamed_free, he, hf, normalize_eq_of_equiv hc]
  · intro h
    have hn : normalizeNamed p ≠ none := by
      intro hn
      have hs := (normalizeNamed_none p).mp hn
      simp [Expr.hasSort, hs] at hp
    cases he : normalizeNamed p with
    | none => exact False.elim (hn he)
    | some r =>
        exact (normalizeNamed_sound he).trans (normalizeNamed_sound (h.symm.trans he)).symm

end Lisa.Lambda
