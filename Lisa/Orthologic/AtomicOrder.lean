import Lisa.Orthologic.Constraints
import Mathlib.Data.Finset.Lattice.Fold

/-!
Lift a decidable atomic preorder through orthologic.

The search uses only atoms occurring in its two arguments. A finite monotone
valuation extends to the whole atomic preorder by taking finite lower-bound
joins. Consequently, the executable test characterizes a single global order,
independently of which atom list a comparison happens to visit.
-/

namespace Lisa.Orthologic

/-- Preserve evaluation when valuations agree on the occurring atoms. -/
theorem Nnf.eval_congr_on {α L : Type} [Ortholattice L] (p : Nnf α)
    (v w : α → L) (h : p.All (fun a => v a = w a)) : p.eval v = p.eval w := by
  induction p with
  | lit a s => cases s <;> simp_all [Nnf.All, Nnf.eval]
  | _ => simp_all [Nnf.All, Nnf.eval]

namespace AtomicOrder

variable {α L : Type} [Ortholattice L]

/-- Interpret the atomic preorder monotonically in an ortholattice. -/
def Valid (r : α → α → Prop) (v : α → L) : Prop :=
  ∀ a b, r a b → v a ≤ v b

/-- Extend a finite valuation using the joins of its recorded lower bounds. -/
def extend [DecidableEq α] (atoms : List α) (r : α → α → Prop)
    [DecidableRel r] (v : α → L) (a : α) : L :=
  (atoms.toFinset.filter (fun b => r b a)).sup v

theorem extend_valid [DecidableEq α] (atoms : List α) (r : α → α → Prop)
    [DecidableRel r] [IsTrans α r] (v : α → L) : Valid r (extend atoms r v) := by
  intro a b hab
  apply Finset.sup_le
  intro c hc
  apply Finset.le_sup
  obtain ⟨hc, hca⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨hc, _root_.trans hca hab⟩

theorem extend_eq [DecidableEq α] (atoms : List α) (r : α → α → Prop)
    [DecidableRel r] [Std.Refl r] (v : α → L) (hv : Constraints.Valid atoms r v)
    {a : α} (ha : a ∈ atoms) : extend atoms r v a = v a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    obtain ⟨hb, hba⟩ := Finset.mem_filter.mp hb
    exact hv b (List.mem_toFinset.mp hb) a ha hba
  · exact Finset.le_sup (Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr ha, refl a⟩)

/-- Decide OL over the atomic constraints occurring in the two formulas. -/
def check [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (p q : Nnf α) : Bool :=
  if Nnf.checkNormalizedLe p q then true
  else Constraints.check (p.atoms ++ q.atoms).eraseDups r p q

/-- Characterize executable comparisons by globally monotone interpretations. -/
theorem check_valid [DecidableEq α] (r : α → α → Prop)
    [DecidableRel r] [IsPreorder α r] (p q : Nnf α) :
    check r p q = true ↔
      ∀ (L : Type) [Ortholattice L] (v : α → L), Valid r v → p.eval v ≤ q.eval v := by
  unfold check
  split
  · rename_i h
    simp only [true_iff]
    exact fun _ _ v _ => Nnf.checkNormalizedLe_sound v h
  · let atoms := (p.atoms ++ q.atoms).eraseDups
    have hp : p.All (· ∈ atoms) :=
      Nnf.All.mono p (fun _ ha => by simp [atoms, ha]) p.all_atoms
    have hq : q.All (· ∈ atoms) :=
      Nnf.All.mono q (fun _ ha => by simp [atoms, ha]) q.all_atoms
    rw [Constraints.check_valid _ r (fun hab hbc => _root_.trans hab hbc) p q hp hq]
    constructor
    · intro h L _ v hv
      exact h L v (fun a _ b _ hab => hv a b hab)
    · intro h L _ v hv
      have extension := h L (extend atoms r v) (extend_valid atoms r v)
      have agree (a : α) (ha : a ∈ atoms) := extend_eq atoms r v hv ha
      rw [p.eval_congr_on _ v (Nnf.All.mono p agree hp),
        q.eval_congr_on _ v (Nnf.All.mono q agree hq)] at extension
      exact extension

end AtomicOrder

end Lisa.Orthologic
