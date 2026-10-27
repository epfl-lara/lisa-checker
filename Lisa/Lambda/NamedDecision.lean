import Lisa.Lambda.NamedReflection
import Lisa.Lambda.Substitution
import Lisa.Lambda.Decision

/-! Named conversion decisions and canonical named output, with exact
malformed-input behavior and shared-conversion correctness. -/
namespace Lisa.Lambda

theorem interpretNamed_none (p : Expr) : interpretNamed p Names.free = none ↔ p.sort = none := by
  rw [← interpretNamed_sort p Names.free]
  exact Option.map_eq_none_iff.symm

/-- Compare canonical typed results without reconstructing names. -/

def compareNamed (p q : Expr) : Option Bool :=
  Packed.compare (interpretNamed p Names.free) (interpretNamed q Names.free)

theorem compareNamed_true : compareNamed p q = some true ↔ AlphaBetaEta p q ∧ p.wellSorted := by
  constructor
  · intro h
    obtain ⟨s, e, f, hp, hq, he⟩ := (Packed.compare_true _ _).mp h
    exact ⟨(AlphaBetaEta.alpha (alpha_reify_of_interpretNamed hp Context.empty)).trans
      ((he.reify Context.empty).trans (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed hq Context.empty)).symm),
      Option.isSome_iff_exists.mpr ⟨s, hasSort_of_interpretNamed hp⟩⟩
  · rintro ⟨hc, hp⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨e, he⟩ := interpretNamed_sorted hs Names.free
    obtain ⟨f, hf⟩ := interpretNamed_sorted (hc.preserves_sort.symm.trans hs) Names.free
    have ht := interpretNamed_alphaBetaEta hc Names.free
    rw [he, hf] at ht
    cases ht with
    | some ht => exact (Packed.compare_true _ _).mpr ⟨s, e, f, he, hf, ht⟩

theorem compareNamed_none (p q : Expr) : compareNamed p q = none ↔ p.sort = none ∨ q.sort = none := by
  rw [compareNamed, Packed.compare_none, interpretNamed_none, interpretNamed_none]

theorem compareNamed_false : compareNamed p q = some false ↔ p.wellSorted ∧ q.wellSorted ∧ ¬ AlphaBetaEta p q := by
  constructor
  · intro h
    have hn : compareNamed p q ≠ none := by simp [h]
    have he := fun hc => hn ((compareNamed_none p q).mpr hc)
    have hp := Option.isSome_iff_ne_none.mpr (not_or.mp he).1
    exact ⟨hp, Option.isSome_iff_ne_none.mpr (not_or.mp he).2,
      fun hc => by simpa [h] using compareNamed_true.mpr ⟨hc, hp⟩⟩
  · rintro ⟨hp, hq, hc⟩
    cases h : compareNamed p q with
    | none => rcases (compareNamed_none p q).mp h with h | h <;> simp_all [Expr.wellSorted]
    | some b => cases b with
      | false => rfl
      | true => exact False.elim (hc (compareNamed_true.mp h).1)

abbrev SortedExpr (s : LSort) := {e : Expr // e.hasSort s}

def SortedExpr.Equivalent (p q : SortedExpr s) : Prop := AlphaBetaEta p.val q.val

instance : DecidableRel (SortedExpr.Equivalent (s := s)) := fun p q =>
  if h : compareNamed p q = some true then isTrue (compareNamed_true.mp h).1
  else isFalse fun hc => h (compareNamed_true.mpr ⟨hc, Option.isSome_iff_exists.mpr ⟨s, p.property⟩⟩)

def normalizeNamed (p : Expr) : Option Expr :=
  (interpretNamed p Names.free).map fun ⟨_, e⟩ => (normalize e).reify Context.empty

theorem normalizeNamed_alpha (h : AlphaEq p q) : normalizeNamed p = normalizeNamed q := by
  unfold normalizeNamed
  rw [interpretNamed_alpha h]

theorem normalizeNamed_sound (h : normalizeNamed p = some q) : AlphaBetaEta p q := by
  cases he : interpretNamed p Names.free with
  | none => simp [normalizeNamed, he] at h
  | some e =>
    rcases e with ⟨s, e⟩
    simp only [normalizeNamed, he, Option.map_some, Option.some.injEq] at h
    subst q
    exact (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed he Context.empty)).trans ((normalize_sound e).reify Context.empty)

theorem normalizeNamed_sort (h : normalizeNamed p = some q) : p.sort = q.sort :=
  (normalizeNamed_sound h).preserves_sort

theorem normalizeNamed_none (p : Expr) : normalizeNamed p = none ↔ p.sort = none := by
  rw [normalizeNamed, Option.map_eq_none_iff, interpretNamed_none]

theorem normalizeNamed_reify (e : Term s) (ρ : Context) :
    normalizeNamed (e.reify ρ) = some ((normalize (e.subst ρ.toSub)).reify Context.empty) := by simp [normalizeNamed]

theorem normalizeNamed_idempotent (h : normalizeNamed p = some q) : normalizeNamed q = some q := by
  cases he : interpretNamed p Names.free with
  | none => simp [normalizeNamed, he] at h
  | some e =>
    rcases e with ⟨s, e⟩
    simp only [normalizeNamed, he, Option.map_some, Option.some.injEq] at h
    subst q
    rw [normalizeNamed_reify, normalize_subst, subst_of_interpretNamed he]

theorem alphaBetaEta_iff_normalizeNamed_eq (hp : p.hasSort s) : AlphaBetaEta p q ↔ normalizeNamed p = normalizeNamed q := by
  constructor
  · intro hc
    obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
    obtain ⟨f, hf⟩ := interpretNamed_sorted (hc.preserves_sort.symm.trans hp) Names.free
    have ht := interpretNamed_alphaBetaEta hc Names.free
    rw [he, hf] at ht
    cases ht with
    | some ht => simp [normalizeNamed, he, hf, normalize_eq_of_equiv ht]
  · intro h
    have hn : normalizeNamed p ≠ none := fun hn => by
      have hs := (normalizeNamed_none p).mp hn
      simp [Expr.hasSort, hs] at hp
    cases he : normalizeNamed p with
    | none => exact False.elim (hn he)
    | some r => exact (normalizeNamed_sound he).trans (normalizeNamed_sound (h.symm.trans he)).symm
end Lisa.Lambda
