import Lisa.Lambda.Normalization

/-! Canonical typed comparison, shared by the two untyped entry points. -/
namespace Lisa.Lambda

instance : DecidableRel (@Equiv s) := fun e f =>
  decidable_of_iff (normalize e = normalize f) (equiv_iff_normalize_eq e f).symm

namespace Packed
/-- Share malformed-input and dynamic-sort handling across raw and named APIs. -/

def compare (p q : Option Expr) : Option Bool := do
  let ⟨s, p⟩ ← p
  let ⟨t, q⟩ ← q
  if h : t = s then some (decide (Equiv p (h ▸ q))) else some false

@[simp] theorem compare_same (p q : Term s) :
    compare (some ⟨s, p⟩) (some ⟨s, q⟩) = some (decide (Equiv p q)) := by simp [compare]

theorem compare_true (p q : Option Expr) : compare p q = some true ↔
    ∃ s, ∃ e f : Term s, p = some ⟨s, e⟩ ∧ q = some ⟨s, f⟩ ∧ Equiv e f := by
  constructor
  · intro h
    cases p with
    | none => simp [compare] at h
    | some p =>
      rcases p with ⟨s, e⟩
      cases q with
      | none => simp [compare] at h
      | some q =>
        rcases q with ⟨t, f⟩
        by_cases hs : t = s
        · subst t; exact ⟨s, e, f, rfl, rfl, by simpa [compare] using h⟩
        · simp [compare, hs] at h
  · rintro ⟨s, e, f, rfl, rfl, h⟩; simp [h]

theorem compare_none (p q : Option Expr) : compare p q = none ↔ p = none ∨ q = none := by
  cases p with
  | none => simp [compare]
  | some p =>
    rcases p with ⟨s, e⟩
    cases q with
    | none => simp [compare]
    | some q =>
      rcases q with ⟨t, f⟩
      by_cases hs : t = s <;> simp [compare, hs]
end Packed
end Lisa.Lambda
