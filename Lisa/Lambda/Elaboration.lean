import Lisa.Lambda.Erasure
import Lisa.Lambda.Decision

/-! Raw applications are checked once before entering the total typed normalizer. -/
namespace Lisa.Lambda
/-- Check raw application sorts. Ambient indices are legitimate sorted variables. -/

def elaborate : RawTerm → Option Packed.Expr
  | .bound n s => some ⟨s, .bound n⟩
  | .free x => some ⟨x.sort, .free x.id⟩
  | .const c => some ⟨c.sort, .const c.id⟩
  | .app f a => do let f ← elaborate f; let a ← elaborate a; Packed.app f a
  | .lam s b => (elaborate b).map (Packed.lam s)

@[simp] theorem elaborate_erase (e : Term s) : elaborate e.erase = some ⟨s, e⟩ := by
  induction e with
  | app f a ihf iha => simp [Term.erase, elaborate, ihf, iha, Packed.app]
  | lam b e ih => simp [Term.erase, elaborate, ih, Packed.lam]
  | _ => rfl

theorem elaborate_sound {e : RawTerm} {t : Term s}
    (h : elaborate e = some ⟨s, t⟩) : t.erase = e := by
  induction e generalizing s with
  | bound => cases h; rfl
  | free => cases h; rfl
  | const => cases h; rfl
  | lam u b ih =>
      cases hb : elaborate b with
      | none => simp [elaborate, hb] at h
      | some w =>
        rcases w with ⟨r, v⟩
        simp only [elaborate, hb, Option.map_some, Packed.lam, Option.some.injEq] at h
        cases h; exact congrArg (RawTerm.lam u) (ih hb)
  | app f a ihf iha =>
      cases hf : elaborate f with
      | none => simp [elaborate, hf] at h
      | some w =>
        rcases w with ⟨r, v⟩
        cases ha : elaborate a with
        | none => simp [elaborate, hf, ha] at h
        | some w =>
          rcases w with ⟨u, a'⟩
          cases r with
          | ind => simp [elaborate, hf, ha, Packed.app] at h
          | prop => simp [elaborate, hf, ha, Packed.app] at h
          | arrow b r =>
            by_cases hu : u = b
            · subst u
              simp [elaborate, hf, ha, Packed.app] at h
              obtain ⟨rfl, ht⟩ := h; cases ht
              simp only [Term.erase, ihf hf, iha ha]
            · simp [elaborate, hf, ha, Packed.app, hu] at h

theorem Term.erase_injective : Function.Injective (@Term.erase s) := by
  intro e f h; simpa using congrArg elaborate h

def normalizeNameless (e : RawTerm) : Option RawTerm :=
  (elaborate e).map fun ⟨_, t⟩ => (normalize t).erase

theorem normalizeNameless_none (e : RawTerm) : normalizeNameless e = none ↔ elaborate e = none :=
  Option.map_eq_none_iff

@[simp] theorem normalizeNameless_erase (e : Term s) :
    normalizeNameless e.erase = some (normalize e).erase := by simp [normalizeNameless]

theorem normalizeNameless_idempotent (h : normalizeNameless e = some n) :
    normalizeNameless n = some n := by
  cases he : elaborate e with
  | none => simp [normalizeNameless, he] at h
  | some w =>
    rcases w with ⟨s, t⟩
    simp [normalizeNameless, he] at h
    subst n; simp

def compareNameless (p q : RawTerm) : Option Bool := Packed.compare (elaborate p) (elaborate q)

def NamelessEquiv (p q : RawTerm) : Prop :=
  ∃ s, ∃ e f : Term s, elaborate p = some ⟨s, e⟩ ∧ elaborate q = some ⟨s, f⟩ ∧ Equiv e f

theorem compareNameless_true (p q : RawTerm) : compareNameless p q = some true ↔ NamelessEquiv p q :=
  Packed.compare_true _ _

theorem compareNameless_none (p q : RawTerm) :
    compareNameless p q = none ↔ elaborate p = none ∨ elaborate q = none := Packed.compare_none _ _

@[simp] theorem compareNameless_erase (p q : Term s) :
    compareNameless p.erase q.erase = some (decide (Equiv p q)) := by simp [compareNameless]

theorem compareNameless_correct (p q : Term s) : compareNameless p.erase q.erase = some true ↔ Equiv p q := by simp
end Lisa.Lambda
