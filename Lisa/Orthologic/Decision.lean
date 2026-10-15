import Lisa.Orthologic.NormalizationComplete

/-! Decide pure orthologic by normalization and structural containment. -/

namespace Lisa.Orthologic.Calculus

variable {α : Type} [DecidableEq α]

/-- Decide derivability without a search or saturation fallback. -/
def decideLe (p q : Nnf α) : Bool := Nnf.checkNormalizedLe p q

theorem decideLe_iff (p q : Nnf α) : decideLe p q = true ↔ Derives p q :=
  Nnf.checkNormalizedLe_iff p q

theorem decideLe_sound (p q : Nnf α) (h : decideLe p q = true) : Derives p q :=
  (decideLe_iff p q).mp h

theorem decideLe_complete (p q : Nnf α) (h : Derives p q) : decideLe p q = true :=
  (decideLe_iff p q).mpr h

instance : DecidableRel (Derives (α := α)) := fun p q =>
  decidable_of_iff (decideLe p q = true) (decideLe_iff p q)

/-- Characterize acceptance by validity in every ortholattice. -/
theorem decideLe_valid (p q : Nnf α) : decideLe p q = true ↔
    ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ q.eval v := by
  rw [decideLe_iff]
  exact ⟨fun h _ _ v => h.sound v, complete p q⟩

/-- Preserve the decision when normalizing either operand. -/
theorem decideLe_normalize (p q : Nnf α) :
    decideLe p.normalize q.normalize = decideLe p q := by
  apply Bool.eq_iff_iff.mpr
  simp only [decideLe_valid, Nnf.eval_normalize]

end Lisa.Orthologic.Calculus

namespace Lisa.Orthologic.Orthogonal

variable {α : Type} [DecidableEq α]

theorem iff_decideLe (p q : Nnf α) :
    Orthogonal p q ↔ Calculus.decideLe p q.compl = true := by
  rw [iff_valid, Calculus.decideLe_valid]
  simp only [Nnf.eval_compl]

instance : DecidableRel (@Orthogonal α) := fun p q =>
  decidable_of_iff (Calculus.decideLe p q.compl = true) (iff_decideLe p q).symm

end Lisa.Orthologic.Orthogonal
