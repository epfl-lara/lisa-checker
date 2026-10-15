import Lisa.Orthologic.Calculus
import Mathlib.Data.Finset.Prod

namespace Lisa.Orthologic.Calculus.Reference

variable {α : Type} [DecidableEq α]

abbrev Key (α : Type) := Position α × Position α

/-- Recognize one cut-free inference whose premises are already in the table. -/
def enabled (table : Finset (Key α)) (g d : Position α) : Bool :=
  (match g with
    | some p => decide (d = some p.compl)
    | none => false) ||
  decide (g = some .bot) ||
  decide ((g, none) ∈ table) ||
  (match d with
    | none => decide ((g, g) ∈ table)
    | some _ => false) ||
  (match g with
    | some (.meet p _) => decide ((some p, d) ∈ table)
    | _ => false) ||
  (match g with
    | some (.meet _ q) => decide ((some q, d) ∈ table)
    | _ => false) ||
  (match g with
    | some (.join p q) => decide ((some p, d) ∈ table ∧ (some q, d) ∈ table)
    | _ => false) ||
  decide ((d, g) ∈ table)

theorem enabled_sound {table : Finset (Key α)}
    (sound : ∀ k ∈ table, Nonempty (Proof false k.1 k.2))
    {g d} (h : enabled table g d = true) : Nonempty (Proof false g d) := by
  simp only [enabled, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h
  · cases g with
    | none => simp at h
    | some p =>
      simp only [decide_eq_true_eq] at h
      subst d
      exact ⟨.ax p⟩
  · subst g; exact ⟨.bot d⟩
  · exact (sound _ h).map Proof.weaken
  · cases d with
    | none =>
      simp only [decide_eq_true_eq] at h
      exact (sound _ h).map Proof.contract
    | some p => simp at h
  · cases g with
    | none => simp at h
    | some p =>
      cases p <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
      exact (sound _ h).map Proof.meetLeft
  · cases g with
    | none => simp at h
    | some p =>
      cases p <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
      exact (sound _ h).map Proof.meetRight
  · cases g with
    | none => simp at h
    | some p =>
      cases p <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at h
      obtain ⟨hp⟩ := sound _ h.1
      obtain ⟨hq⟩ := sound _ h.2
      exact ⟨.join hp hq⟩
  · exact (sound _ h).map Proof.swap

/-- Retain a finite set of positions closed under backward rule decomposition. -/
structure Support (α : Type) [DecidableEq α] where
  positions : Finset (Position α)
  empty : none ∈ positions
  meet : ∀ {p q}, some (.meet p q) ∈ positions →
    some p ∈ positions ∧ some q ∈ positions
  join : ∀ {p q}, some (.join p q) ∈ positions →
    some p ∈ positions ∧ some q ∈ positions

/-- Retain only certified sequents over the finite support. -/
structure Table (support : Support α) where
  entries : Finset (Key α)
  bounded : entries ⊆ support.positions ×ˢ support.positions
  sound : ∀ k ∈ entries, Nonempty (Proof false k.1 k.2)

namespace Table

def empty (support : Support α) : Table support :=
  ⟨∅, Finset.empty_subset _, by simp⟩

def extend {support : Support α} (table : Table support) : Table support where
  entries := table.entries ∪ (support.positions ×ˢ support.positions).filter
    (fun k => enabled table.entries k.1 k.2 = true)
  bounded := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact table.bounded hk
    · exact (Finset.mem_filter.mp hk).1
  sound := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact table.sound k hk
    · exact enabled_sound table.sound (Finset.mem_filter.mp hk).2

theorem subset_extend {support : Support α} (table : Table support) :
    table.entries ⊆ table.extend.entries := Finset.subset_union_left

end Table

/-- Retain a saturated table and erase the certificate of closure. -/
structure Closed (support : Support α) extends Table support where
  closed : ∀ {g d}, g ∈ support.positions → d ∈ support.positions →
    enabled entries g d = true → (g, d) ∈ entries

/-- Saturate until no sequent is added; finite support proves termination. -/
def saturate {support : Support α} (table : Table support) : Closed support :=
  let next := table.extend
  if h : next.entries = table.entries then
    { toTable := table
      closed := by
        intro g d hg hd henabled
        rw [← h]
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hg, hd⟩, henabled⟩) }
  else saturate next
termination_by (support.positions ×ˢ support.positions).card - table.entries.card
decreasing_by
  have hsubset := table.subset_extend
  have hcard := Finset.card_le_card table.extend.bounded
  have hstrict : table.entries ⊂ table.extend.entries :=
    lt_of_le_of_ne hsubset (Ne.symm h)
  have hlt := Finset.card_lt_card hstrict
  omega

/-- Every cut-free proof over the support is discovered by saturation. -/
theorem Closed.complete {support : Support α} (table : Closed support)
    {g d} (h : Proof false g d) :
    g ∈ support.positions → d ∈ support.positions → (g, d) ∈ table.entries := by
  induction h with
  | ax p =>
    intro hg hd
    apply table.closed hg hd
    simp [enabled]
  | bot d =>
    intro hg hd
    apply table.closed hg hd
    simp [enabled]
  | weaken h ih =>
    intro hg hd
    have hp := ih hg support.empty
    apply table.closed hg hd
    simp [enabled, hp]
  | contract h ih =>
    intro hg hd
    have hp := ih hg hg
    apply table.closed hg hd
    simp [enabled, hp]
  | meetLeft h ih =>
    intro hg hd
    have hp := ih (support.meet hg).1 hd
    apply table.closed hg hd
    simp [enabled, hp]
  | meetRight h ih =>
    intro hg hd
    have hp := ih (support.meet hg).2 hd
    apply table.closed hg hd
    simp [enabled, hp]
  | join h k ih ik =>
    intro hg hd
    have hp := ih (support.join hg).1 hd
    have hq := ik (support.join hg).2 hd
    apply table.closed hg hd
    simp [enabled, hp, hq]
  | swap h ih =>
    intro hg hd
    have hp := ih hd hg
    apply table.closed hg hd
    simp [enabled, hp]
  | cut h _ _ _ _ => cases h

end Lisa.Orthologic.Calculus.Reference
