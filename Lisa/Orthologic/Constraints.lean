import Lisa.Orthologic.Decision
import Lisa.Orthologic.Substitution

/-!
Reduce finitely many atomic inequalities to pure orthologic.
Replace each atom by its meet with the atoms known to lie above it.
This replacement fixes every valuation satisfying the inequalities.
For a preorder, it also satisfies the inequalities under every valuation.
-/

namespace Lisa.Orthologic

/-- Require each atom of a formula to satisfy a predicate. -/
def Nnf.All {α : Type} (P : α → Prop) : Nnf α → Prop
  | .lit a _ => P a
  | .bot | .top => True
  | .meet p q | .join p q => p.All P ∧ q.All P

theorem Nnf.All.mono {α : Type} {P Q : α → Prop} (p : Nnf α)
    (h : ∀ a, P a → Q a) : p.All P → p.All Q := by
  induction p <;> simp_all [Nnf.All]

/-- Collect atom occurrences without requiring a hash or ordering instance. -/
def Nnf.atoms {α : Type} : Nnf α → List α
  | .lit a _ => [a]
  | .bot | .top => []
  | .meet p q | .join p q => p.atoms ++ q.atoms

theorem Nnf.all_atoms {α : Type} (p : Nnf α) : p.All (· ∈ p.atoms) := by
  induction p with
  | lit a s => simp [All, atoms]
  | bot | top => trivial
  | meet p q hp hq | join p q hp hq =>
    exact ⟨All.mono p (fun _ h => List.mem_append_left _ h) hp,
      All.mono q (fun _ h => List.mem_append_right _ h) hq⟩

theorem Nnf.eval_bind_eq {α β L : Type} [Ortholattice L]
    (f : α → Nnf β) (v : β → L) (w : α → L) (p : Nnf α)
    (h : p.All (fun a => (f a).eval v = w a)) :
    (p.bind f).eval v = p.eval w := by
  rw [Nnf.eval_bind]
  induction p with
  | lit a s => cases s <;> simp_all [Nnf.All, Nnf.eval]
  | _ => simp_all [Nnf.All, Nnf.eval]

namespace Constraints

variable {α L : Type} [Ortholattice L]

/-- Meet a finite list without imposing an order on its atoms. -/
def meet : List (Nnf α) → Nnf α
  | [] => .top
  | p :: ps => .meet p (meet ps)

theorem le_eval_meet (v : α → L) (x : L) (ps : List (Nnf α)) :
    x ≤ (meet ps).eval v ↔ ∀ p ∈ ps, x ≤ p.eval v := by
  induction ps with
  | nil => simp [meet, Nnf.eval]
  | cons p ps ih => simp [meet, Nnf.eval, le_inf_iff, ih]

/-- Interpret the listed atomic constraints in an arbitrary ortholattice. -/
def Valid (atoms : List α) (r : α → α → Prop) (v : α → L) : Prop :=
  ∀ a ∈ atoms, ∀ b ∈ atoms, r a b → v a ≤ v b

/-- Add the recorded upper bounds to an atom, retaining the atom itself. -/
def encode (atoms : List α) (r : α → α → Prop) [DecidableRel r] (a : α) : Nnf α :=
  .meet (.lit a false) (meet ((atoms.filter (r a)).map (fun b => .lit b false)))

theorem eval_encode (atoms : List α) (r : α → α → Prop) [DecidableRel r]
    (v : α → L) (hv : Valid atoms r v) {a : α} (ha : a ∈ atoms) :
    (encode atoms r a).eval v = v a := by
  apply le_antisymm inf_le_left
  apply le_inf le_rfl
  rw [le_eval_meet]
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
  exact hv a ha b (List.mem_filter.mp hb).1 (of_decide_eq_true (List.mem_filter.mp hb).2)

theorem eval_encode_formula (atoms : List α) (r : α → α → Prop) [DecidableRel r]
    (v : α → L) (hv : Valid atoms r v) (p : Nnf α)
    (hp : p.All (· ∈ atoms)) :
    (p.bind (encode atoms r)).eval v = p.eval v := by
  apply Nnf.eval_bind_eq
  induction p with
  | lit a s => exact eval_encode atoms r v hv hp
  | _ => simp_all [Nnf.All]

/-- Show that the encoding enforces every edge of a transitive relation. -/
theorem encoded_valid (atoms : List α) (r : α → α → Prop) [DecidableRel r]
    (trans : ∀ {a b c}, r a b → r b c → r a c) (v : α → L) :
    Valid atoms r (fun a => (encode atoms r a).eval v) := by
  intro a _ b hb hab
  have upper : ∀ c ∈ atoms, r a c → (encode atoms r a).eval v ≤ v c := by
    intro c hc hac
    apply le_trans inf_le_right
    exact (le_eval_meet v _ _).mp le_rfl (.lit c false)
      (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, decide_eq_true hac⟩, rfl⟩)
  apply le_inf (upper b hb hab)
  rw [le_eval_meet]
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact upper c (List.mem_filter.mp hc).1
    (trans hab (of_decide_eq_true (List.mem_filter.mp hc).2))

/-- Decide OL after adding a finite set of atomic upper bounds. -/
def check [DecidableEq α] (atoms : List α) (r : α → α → Prop) [DecidableRel r]
    (p q : Nnf α) : Bool :=
  Calculus.decideLe (p.bind (encode atoms r)) (q.bind (encode atoms r))

theorem check_sound [DecidableEq α] (atoms : List α) (r : α → α → Prop)
    [DecidableRel r] (p q : Nnf α) (hp : p.All (· ∈ atoms)) (hq : q.All (· ∈ atoms))
    (h : check atoms r p q = true) (v : α → L) (hv : Valid atoms r v) :
    p.eval v ≤ q.eval v := by
  have h' := (Calculus.decideLe_sound _ _ h).sound v
  simpa only [eval_encode_formula atoms r v hv p hp,
    eval_encode_formula atoms r v hv q hq] using h'

/-- Complete the reduction for a transitive atomic order. -/
theorem check_complete [DecidableEq α] (atoms : List α) (r : α → α → Prop)
    [DecidableRel r] (trans : ∀ {a b c}, r a b → r b c → r a c) (p q : Nnf α)
    (h : ∀ (L : Type) [Ortholattice L] (v : α → L),
      Valid atoms r v → p.eval v ≤ q.eval v) : check atoms r p q = true := by
  apply Calculus.decideLe_complete
  apply Calculus.complete
  intro L _ v
  simpa only [Nnf.eval_bind] using h L (fun a => (encode atoms r a).eval v)
    (encoded_valid atoms r trans v)

/-- Characterize finite constrained validity by normalized comparison. -/
theorem check_valid [DecidableEq α] (atoms : List α) (r : α → α → Prop)
    [DecidableRel r] (trans : ∀ {a b c}, r a b → r b c → r a c) (p q : Nnf α)
    (hp : p.All (· ∈ atoms)) (hq : q.All (· ∈ atoms)) :
    check atoms r p q = true ↔
      ∀ (L : Type) [Ortholattice L] (v : α → L),
        Valid atoms r v → p.eval v ≤ q.eval v :=
  ⟨fun h _ _ v hv => check_sound atoms r p q hp hq h v hv,
    check_complete atoms r trans p q⟩

end Constraints

end Lisa.Orthologic
