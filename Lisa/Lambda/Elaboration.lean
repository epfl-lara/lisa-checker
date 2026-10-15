import Lisa.Lambda.Decision
import Lisa.Lambda.Erasure

namespace Lisa.Lambda

namespace Var

/-- Recover a sorted binder from its de Bruijn index. -/
def lookup : (Γ : List LSort) → Nat → Option (Σ s, Var Γ s)
  | [], _ => none
  | s :: _, 0 => some ⟨s, .here⟩
  | _ :: Γ, n + 1 => (lookup Γ n).map (fun ⟨s, v⟩ => ⟨s, .there v⟩)

@[simp] theorem lookup_index (v : Var Γ s) : lookup Γ (Term.index v) = some ⟨s, v⟩ := by
  induction v with
  | here => rfl
  | there v ih => simp [lookup, Term.index, ih]

theorem lookup_sound {Γ : List LSort} {n s} {v : Var Γ s}
    (h : lookup Γ n = some ⟨s, v⟩) : Term.index v = n := by
  induction Γ generalizing n with
  | nil => simp [lookup] at h
  | cons t Γ ih =>
      cases n with
      | zero => cases h; rfl
      | succ n =>
          cases hv : lookup Γ n with
          | none => simp [lookup, hv] at h
          | some w =>
              cases w with
              | mk u w =>
                  simp only [lookup, hv, Option.map_some, Option.some.injEq] at h
                  cases h
                  exact congrArg Nat.succ (ih hv)

end Var

/-- Check binder scopes and application sorts before entering the total normalizer. -/
def elaborate (Γ : List LSort) : NamelessExpr → Option (Σ s, Term Γ s)
  | .free x => some ⟨x.sort, .free x.id⟩
  | .const c => some ⟨c.sort, .const c.id⟩
  | .bound n s => do
      let ⟨t, v⟩ ← Var.lookup Γ n
      if h : s = t then some ⟨s, .bound (h ▸ v)⟩ else none
  | .app f a => do
      let ⟨fs, f⟩ ← elaborate Γ f
      match fs with
      | .arrow s t =>
          let ⟨u, a⟩ ← elaborate Γ a
          if h : u = s then some ⟨t, .app f (h ▸ a)⟩ else none
      | _ => none
  | .lam s b => do
      let ⟨t, b⟩ ← elaborate (s :: Γ) b
      some ⟨s >> t, .lam b⟩

/-- Accept every erased sorted term without changing any of its syntax. -/
@[simp] theorem elaborate_erase (e : Term Γ s) :
    elaborate Γ e.erase = some ⟨s, e⟩ := by
  induction e with
  | bound v => simp [elaborate, Term.erase]
  | free => rfl
  | const => rfl
  | app f a ihf iha => simp [elaborate, Term.erase, ihf, iha]
  | lam b ih => simp [elaborate, Term.erase, ih]

/-- Preserve the exact nameless syntax of every successfully elaborated input. -/
theorem elaborate_sound {e : NamelessExpr} {t : Term Γ s}
    (h : elaborate Γ e = some ⟨s, t⟩) : t.erase = e := by
  induction e generalizing Γ s with
  | free x => cases h; rfl
  | const c => cases h; rfl
  | bound n u =>
      cases hv : Var.lookup Γ n with
      | none => simp [elaborate, hv] at h
      | some w =>
          rcases w with ⟨r, v⟩
          by_cases hu : u = r
          · subst u
            simp [elaborate, hv] at h
            obtain ⟨rfl, ht⟩ := h
            cases ht
            exact congrArg (fun n => NamelessExpr.bound n r) (Var.lookup_sound hv)
          · simp [elaborate, hv, hu] at h
  | lam u b ih =>
      cases hb : elaborate (u :: Γ) b with
      | none => simp [elaborate, hb] at h
      | some w =>
          rcases w with ⟨r, v⟩
          simp [elaborate, hb] at h
          obtain ⟨rfl, ht⟩ := h
          cases ht
          exact congrArg (NamelessExpr.lam u) (ih hb)
  | app f a ihf iha =>
      cases hf : elaborate Γ f with
      | none => simp [elaborate, hf] at h
      | some w =>
          rcases w with ⟨r, v⟩
          cases r with
          | ind => simp [elaborate, hf] at h
          | prop => simp [elaborate, hf] at h
          | arrow u r =>
              cases ha : elaborate Γ a with
              | none => simp [elaborate, hf, ha] at h
              | some w =>
                  rcases w with ⟨w, a'⟩
                  by_cases hu : w = u
                  · subst w
                    simp [elaborate, hf, ha] at h
                    obtain ⟨rfl, ht⟩ := h
                    cases ht
                    exact congrArg₂ NamelessExpr.app (ihf hf) (iha ha)
                  · simp [elaborate, hf, ha, hu] at h

/-- Normalize sorted, scoped input and reject malformed records explicitly. -/
def normalizeNameless (Γ : List LSort) (e : NamelessExpr) : Option NamelessExpr :=
  (elaborate Γ e).map (fun ⟨_, t⟩ => (normalize t).erase)

@[simp] theorem normalizeNameless_erase (e : Term Γ s) :
    normalizeNameless Γ e.erase = some (normalize e).erase := by
  simp [normalizeNameless]

/-- Preserve canonical readback when normalizing an already normalized record. -/
theorem normalizeNameless_idempotent {e n : NamelessExpr}
    (h : normalizeNameless Γ e = some n) : normalizeNameless Γ n = some n := by
  cases he : elaborate Γ e with
  | none => simp [normalizeNameless, he] at h
  | some w =>
      rcases w with ⟨s, t⟩
      simp [normalizeNameless, he] at h
      subst n
      simp

/-- Recover typed syntax uniquely from its erased representation. -/
theorem Term.erase_injective : Function.Injective (@Term.erase Γ s) := by
  intro e f h
  have he := congrArg (elaborate Γ) h
  simpa using he

/-- Compare well-formed records; distinguish malformed inputs from negative answers. -/
def compareNameless (Γ : List LSort) (p q : NamelessExpr) : Option Bool := do
  let ⟨s, p⟩ ← elaborate Γ p
  let ⟨t, q⟩ ← elaborate Γ q
  if h : t = s then some (decide (Equiv p (h ▸ q))) else some false

@[simp] theorem compareNameless_erase (p q : Term Γ s) :
    compareNameless Γ p.erase q.erase = some (decide (Equiv p q)) := by
  simp [compareNameless]

theorem compareNameless_correct (p q : Term Γ s) :
    compareNameless Γ p.erase q.erase = some true ↔ Equiv p q := by
  simp

/-- Relate records only when both elaborate at the same sort and their terms convert. -/
def NamelessEquiv (Γ : List LSort) (p q : NamelessExpr) : Prop :=
  ∃ s, ∃ e f : Term Γ s,
    elaborate Γ p = some ⟨s, e⟩ ∧ elaborate Γ q = some ⟨s, f⟩ ∧ Equiv e f

/-- Characterize every positive answer, including dynamically checked inputs. -/
theorem compareNameless_true (Γ : List LSort) (p q : NamelessExpr) :
    compareNameless Γ p q = some true ↔ NamelessEquiv Γ p q := by
  constructor
  · intro h
    cases hp : elaborate Γ p with
    | none => simp [compareNameless, hp] at h
    | some e =>
        rcases e with ⟨s, e⟩
        cases hq : elaborate Γ q with
        | none => simp [compareNameless, hp, hq] at h
        | some f =>
            rcases f with ⟨t, f⟩
            by_cases hs : t = s
            · subst t
              simp [compareNameless, hp, hq] at h
              exact ⟨s, e, f, hp, hq, h⟩
            · simp [compareNameless, hp, hq, hs] at h
  · rintro ⟨s, e, f, hp, hq, h⟩
    simp [compareNameless, hp, hq, h]

/-- Reserve failure for malformed records, not exhausted search. -/
theorem compareNameless_none (Γ : List LSort) (p q : NamelessExpr) :
    compareNameless Γ p q = none ↔ elaborate Γ p = none ∨ elaborate Γ q = none := by
  cases hp : elaborate Γ p with
  | none => simp [compareNameless, hp]
  | some e =>
      rcases e with ⟨s, e⟩
      cases hq : elaborate Γ q with
      | none => simp [compareNameless, hp, hq]
      | some f =>
          rcases f with ⟨t, f⟩
          by_cases hs : t = s <;> simp [compareNameless, hp, hq, hs]

/-- Keep alpha-equivalent named inputs indistinguishable at the elaboration boundary. -/
theorem normalizeNameless_alpha {p q : Expr} (h : AlphaEq p q) :
    normalizeNameless [] (p.toNameless []) = normalizeNameless [] (q.toNameless []) :=
  congrArg (normalizeNameless []) (congrArg Prod.fst h)

end Lisa.Lambda
