import Lisa.Orthologic.Decision
import Lisa.Orthologic.Reference.Saturation

namespace Lisa.Orthologic.Calculus.Reference

variable {α : Type} [DecidableEq α]

/-- Collect the formulas that can occur in backward cut-free search. -/
def subterms : Nnf α → Finset (Nnf α)
  | .lit a s => {.lit a s}
  | .bot => {.bot}
  | .top => {.top}
  | .meet p q => insert (.meet p q) (subterms p ∪ subterms q)
  | .join p q => insert (.join p q) (subterms p ∪ subterms q)

@[simp] theorem mem_subterms (p : Nnf α) : p ∈ subterms p := by
  cases p <;> simp [subterms]

theorem subterms_subset {p q : Nnf α} (h : q ∈ subterms p) :
    subterms q ⊆ subterms p := by
  induction p generalizing q with
  | lit a s =>
    simp only [subterms, Finset.mem_singleton] at h
    subst q
    exact Finset.Subset.refl _
  | bot =>
    simp only [subterms, Finset.mem_singleton] at h
    subst q
    exact Finset.Subset.refl _
  | top =>
    simp only [subterms, Finset.mem_singleton] at h
    subst q
    exact Finset.Subset.refl _
  | meet p r ih ir =>
    simp only [subterms, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Finset.Subset.refl _
    · exact (ih h).trans (fun _ hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_left _ hk))
    · exact (ir h).trans (fun _ hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_right _ hk))
  | join p r ih ir =>
    simp only [subterms, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Finset.Subset.refl _
    · exact (ih h).trans (fun _ hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_left _ hk))
    · exact (ir h).trans (fun _ hk =>
        Finset.mem_insert_of_mem (Finset.mem_union_right _ hk))

private theorem subterms_union_subset {p q r : Nnf α}
    (h : r ∈ subterms p ∪ subterms q) : subterms r ⊆ subterms p ∪ subterms q := by
  rcases Finset.mem_union.mp h with h | h
  · exact (subterms_subset h).trans Finset.subset_union_left
  · exact (subterms_subset h).trans Finset.subset_union_right

/-- Close two roots under subformulas and add the absent position. -/
def support (p q : Nnf α) : Support α where
  positions := insert none ((subterms p ∪ subterms q).image some)
  empty := Finset.mem_insert_self _ _
  meet := by
    intro r s h
    have hroot : .meet r s ∈ subterms p ∪ subterms q := by simpa using h
    have hc := subterms_union_subset hroot
    have hr : r ∈ subterms (.meet r s) := by simp [subterms]
    have hs : s ∈ subterms (.meet r s) := by simp [subterms]
    exact ⟨by simpa using hc hr, by simpa using hc hs⟩
  join := by
    intro r s h
    have hroot : .join r s ∈ subterms p ∪ subterms q := by simpa using h
    have hc := subterms_union_subset hroot
    have hr : r ∈ subterms (.join r s) := by simp [subterms]
    have hs : s ∈ subterms (.join r s) := by simp [subterms]
    exact ⟨by simpa using hc hr, by simpa using hc hs⟩

@[simp] theorem left_mem_support (p q : Nnf α) : some p ∈ (support p q).positions := by
  simp [support]

@[simp] theorem right_mem_support (p q : Nnf α) : some q ∈ (support p q).positions := by
  simp [support]

/-- Decide pure OL validity by finite, certified, cut-free saturation. -/
def decideLe (p q : Nnf α) : Bool :=
  let table := saturate (Table.empty (support p q.compl))
  decide ((some p, some q.compl) ∈ table.entries)

theorem decideLe_sound (p q : Nnf α) (h : decideLe p q = true) : Derives p q := by
  simp only [decideLe, decide_eq_true_eq] at h
  obtain ⟨h'⟩ := (saturate (Table.empty (support p q.compl))).sound _ h
  exact ⟨h'.withCuts⟩

theorem decideLe_complete (p q : Nnf α) (h : Derives p q) : decideLe p q = true := by
  obtain ⟨h⟩ := h
  obtain ⟨h'⟩ := cutFree h
  simp only [decideLe, decide_eq_true_eq]
  exact (saturate (Table.empty (support p q.compl))).complete h'
    (left_mem_support _ _) (right_mem_support _ _)

theorem decideLe_iff (p q : Nnf α) : decideLe p q = true ↔ Derives p q :=
  ⟨decideLe_sound p q, decideLe_complete p q⟩

/-- Characterize acceptance by validity in every ortholattice. -/
theorem decideLe_valid (p q : Nnf α) : decideLe p q = true ↔
    ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ q.eval v := by
  rw [decideLe_iff]
  exact ⟨fun h _ _ v => h.sound v, complete p q⟩

/-- Cross-check the independent saturation procedure against normalized comparison. -/
theorem decideLe_eq (p q : Nnf α) : decideLe p q = Calculus.decideLe p q := by
  apply Bool.eq_iff_iff.mpr
  rw [decideLe_iff, Calculus.decideLe_iff]

end Lisa.Orthologic.Calculus.Reference
