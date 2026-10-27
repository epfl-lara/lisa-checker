import Lisa.Orthologic.Decision
import Lisa.Orthologic.Substitution

namespace Lisa.Orthologic.Calculus

variable {α : Type} [DecidableEq α]

namespace Free

private instance : Ortholattice (Set Unit) where
  compl_antitone := fun _ _ h => compl_le_compl h
  compl_involutive := compl_compl
  sup_compl := fun _ => sup_compl_eq_top

private theorem literals_same (a b : α) (s t : Bool)
    (h : Derives (.lit a s) (.lit b t) ∧ Derives (.lit b t) (.lit a s)) :
    a = b ∧ s = t := by
  have equal (v : α → Set Unit) :=
    le_antisymm (h.1.sound v) (h.2.sound v)
  have polarity := equal (fun _ => ∅)
  have hst : s = t := by
    cases s <;> cases t <;> simp_all [Nnf.eval, Set.ext_iff]
  subst t
  refine ⟨?_, rfl⟩
  by_contra hab
  have separated := equal (fun x => if x = a then Set.univ else ∅)
  cases s <;> simp [Nnf.eval, Ne.symm hab, Set.ext_iff] at separated

/-- Compare quotient values through the complete normalization procedure. -/
def compare : Free α → Free α → Bool :=
  Quotient.lift₂ decideLe (by
    intro p q p' q' hp hq
    apply Bool.eq_iff_iff.mpr
    simp only [decideLe_iff]
    exact ⟨fun h => .trans hp.2 (.trans h hq.1),
      fun h => .trans hp.1 (.trans h hq.2)⟩)

theorem compare_iff (p q : Free α) : compare p q = true ↔ p ≤ q :=
  Quotient.inductionOn₂ p q decideLe_iff

private def equalByOrder (p q : Nnf α) : Bool :=
  if p = q then true else decideLe p q && decideLe q p

private theorem equalByOrder_iff (p q : Nnf α) :
    equalByOrder p q = true ↔ Derives p q ∧ Derives q p := by
  unfold equalByOrder
  split
  · rename_i h
    subst q
    simp only [true_iff]
    exact ⟨.refl p, .refl p⟩
  · simp only [Bool.and_eq_true, decideLe_iff]

private def equalRepresentatives (p q : Nnf α) : Bool :=
  match p, q with
  | .lit a s, .lit b t => decide (a = b ∧ s = t)
  | p, q => equalByOrder p q

private theorem equalRepresentatives_iff (p q : Nnf α) :
    equalRepresentatives p q = true ↔ Derives p q ∧ Derives q p := by
  cases p <;> cases q <;>
    simp only [equalRepresentatives, equalByOrder_iff, decide_eq_true_eq]
  case lit.lit a s b t =>
    exact ⟨by rintro ⟨rfl, rfl⟩; exact ⟨.refl _, .refl _⟩,
      literals_same a b s t⟩

private def quickEqual : Free α → Free α → Bool :=
  Quotient.lift₂ equalRepresentatives (by
    intro p q p' q' hp hq
    apply Bool.eq_iff_iff.mpr
    simp only [equalRepresentatives_iff]
    exact ⟨fun h => ⟨.trans hp.2 (.trans h.1 hq.1),
      .trans hq.2 (.trans h.2 hp.1)⟩,
      fun h => ⟨.trans hp.1 (.trans h.1 hq.2),
        .trans hq.1 (.trans h.2 hp.2)⟩⟩)

private theorem quickEqual_iff (p q : Free α) : quickEqual p q = true ↔ p = q := by
  refine Quotient.inductionOn₂ p q ?_
  intro p q
  exact (equalRepresentatives_iff p q).trans
    (Quotient.eq (r := equivalence α)).symm

/-- Decide literal equality directly; compare other representatives before both order directions. -/
def decEq : DecidableEq (Free α) := fun p q =>
  decidable_of_iff (quickEqual p q = true) (quickEqual_iff p q)

instance : DecidableEq (Free α) := decEq

instance : DecidableLE (Free α) := fun p q =>
  decidable_of_iff (compare p q = true) (compare_iff p q)

end Free
end Lisa.Orthologic.Calculus
