import Lisa.Orthologic.Formula

/-!
Separate bounded-lattice containment from orthologic contraction. This cut-free
relation provides the specification of the structural comparator; signed
literals remain independent generators here.
-/

namespace Lisa.Orthologic.Nnf

variable {α : Type}

/-- Derive containment using only bounded-lattice rules, without contraction. -/
inductive LatticeLe : Nnf α → Nnf α → Prop
  | refl (p) : LatticeLe p p
  | bot (p) : LatticeLe .bot p
  | top (p) : LatticeLe p .top
  | projectLeft {p q r} : LatticeLe p r → LatticeLe (.meet p q) r
  | projectRight {p q r} : LatticeLe q r → LatticeLe (.meet p q) r
  | injectLeft {p q r} : LatticeLe p q → LatticeLe p (.join q r)
  | injectRight {p q r} : LatticeLe p r → LatticeLe p (.join q r)
  | meet {p q r} : LatticeLe p q → LatticeLe p r → LatticeLe p (.meet q r)
  | join {p q r} : LatticeLe p r → LatticeLe q r → LatticeLe (.join p q) r

namespace LatticeLe

/-- Reverse containment by dualizing both expressions. -/
theorem compl {p q : Nnf α} (h : LatticeLe p q) : LatticeLe q.compl p.compl := by
  induction h with
  | refl p => exact .refl _
  | bot p => exact .top _
  | top p => exact .bot _
  | projectLeft _ ih => exact .injectLeft ih
  | projectRight _ ih => exact .injectRight ih
  | injectLeft _ ih => exact .projectLeft ih
  | injectRight _ ih => exact .projectRight ih
  | meet _ _ ih ik => exact .join ih ik
  | join _ _ ih ik => exact .meet ih ik

theorem of_join {p q r : Nnf α} (h : LatticeLe (.join p q) r) :
    LatticeLe p r ∧ LatticeLe q r := by
  generalize he : Nnf.join p q = s at h
  induction h generalizing p q with
  | refl s => cases he; exact ⟨.injectLeft (.refl _), .injectRight (.refl _)⟩
  | bot s => cases he
  | top s => exact ⟨.top _, .top _⟩
  | projectLeft _ _ => cases he
  | projectRight _ _ => cases he
  | injectLeft _ ih => exact ⟨.injectLeft (ih he).1, .injectLeft (ih he).2⟩
  | injectRight _ ih => exact ⟨.injectRight (ih he).1, .injectRight (ih he).2⟩
  | meet _ _ ih ik => exact ⟨.meet (ih he).1 (ik he).1, .meet (ih he).2 (ik he).2⟩
  | join h k _ _ => cases he; exact ⟨h, k⟩

theorem to_meet {p q r : Nnf α} (h : LatticeLe p (.meet q r)) :
    LatticeLe p q ∧ LatticeLe p r := by
  have h' := h.compl.of_join
  constructor
  · simpa only [compl_compl] using h'.1.compl
  · simpa only [compl_compl] using h'.2.compl

theorem of_top {p q : Nnf α} (h : LatticeLe .top q) : LatticeLe p q := by
  generalize he : (Nnf.top : Nnf α) = s at h
  induction h with
  | refl s => cases he; exact .top _
  | bot s => cases he
  | top s => exact .top _
  | projectLeft _ _ => cases he
  | projectRight _ _ => cases he
  | injectLeft _ ih => exact .injectLeft (ih he)
  | injectRight _ ih => exact .injectRight (ih he)
  | meet _ _ ih ik => exact .meet (ih he) (ik he)
  | join _ _ _ _ => cases he

/-- Eliminate a bounded-lattice cut without adding a rule to the relation. -/
theorem trans {p q r : Nnf α} (h : LatticeLe p q) (k : LatticeLe q r) :
    LatticeLe p r := by
  cases h with
  | refl => exact k
  | bot => exact .bot _
  | top => exact k.of_top
  | projectLeft h => exact .projectLeft (h.trans k)
  | projectRight h => exact .projectRight (h.trans k)
  | injectLeft h => exact h.trans k.of_join.1
  | injectRight h => exact h.trans k.of_join.2
  | join h h' => exact .join (h.trans k) (h'.trans k)
  | meet h h' =>
      cases k with
      | refl => exact .meet h h'
      | top => exact .top _
      | projectLeft k => exact h.trans k
      | projectRight k => exact h'.trans k
      | injectLeft k => exact .injectLeft ((LatticeLe.meet h h').trans k)
      | injectRight k => exact .injectRight ((LatticeLe.meet h h').trans k)
      | meet k k' => exact .meet ((LatticeLe.meet h h').trans k) ((LatticeLe.meet h h').trans k')
termination_by p.size + q.size + r.size
decreasing_by
  all_goals
    simp_all only [heq_eq_eq, Nnf.meet.injEq]
    subst_vars
    simp_all only [size]
    omega

/-- Flatten meets for the generalized Whitman decomposition. -/
def meetLeaves : Nnf α → List (Nnf α)
  | .meet p q => meetLeaves p ++ meetLeaves q
  | p => [p]

/-- Flatten joins for the generalized Whitman decomposition. -/
def joinLeaves : Nnf α → List (Nnf α)
  | .join p q => joinLeaves p ++ joinLeaves q
  | p => [p]

theorem size_meetLeaves {p t : Nnf α} (h : t ∈ meetLeaves p) : t.size ≤ p.size := by
  induction p with
  | meet p q ih ik =>
      simp only [meetLeaves, List.mem_append] at h
      rcases h with h | h
      · have := ih h; simp only [size]; omega
      · have := ik h; simp only [size]; omega
  | _ => simp only [meetLeaves, List.mem_singleton] at h; subst t; exact le_rfl

theorem size_joinLeaves {p t : Nnf α} (h : t ∈ joinLeaves p) : t.size ≤ p.size := by
  induction p with
  | join p q ih ik =>
      simp only [joinLeaves, List.mem_append] at h
      rcases h with h | h
      · have := ih h; simp only [size]; omega
      · have := ik h; simp only [size]; omega
  | _ => simp only [joinLeaves, List.mem_singleton] at h; subst t; exact le_rfl

/-- Expose a source factor or target summand witnessing containment. -/
theorem whitman {p q : Nnf α} (h : LatticeLe p q) :
    (∃ t ∈ meetLeaves p, LatticeLe t q) ∨
    (∃ t ∈ joinLeaves q, LatticeLe p t) := by
  induction h with
  | refl p =>
      cases p with
      | meet p q => exact Or.inr ⟨_, by simp [joinLeaves], .refl _⟩
      | _ => exact Or.inl ⟨_, by simp [meetLeaves], .refl _⟩
  | bot p => exact Or.inl ⟨_, by simp [meetLeaves], .bot _⟩
  | top p => exact Or.inr ⟨_, by simp [joinLeaves], .top _⟩
  | projectLeft _ ih =>
      rcases ih with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
      · exact Or.inl ⟨t, List.mem_append_left _ ht, h⟩
      · exact Or.inr ⟨t, ht, .projectLeft h⟩
  | projectRight _ ih =>
      rcases ih with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
      · exact Or.inl ⟨t, List.mem_append_right _ ht, h⟩
      · exact Or.inr ⟨t, ht, .projectRight h⟩
  | injectLeft _ ih =>
      rcases ih with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
      · exact Or.inl ⟨t, ht, .injectLeft h⟩
      · exact Or.inr ⟨t, List.mem_append_left _ ht, h⟩
  | injectRight _ ih =>
      rcases ih with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
      · exact Or.inl ⟨t, ht, .injectRight h⟩
      · exact Or.inr ⟨t, List.mem_append_right _ ht, h⟩
  | meet h k _ _ => exact Or.inr ⟨_, by simp [joinLeaves], .meet h k⟩
  | join h k _ _ => exact Or.inl ⟨_, by simp [meetLeaves], .join h k⟩

end LatticeLe
end Lisa.Orthologic.Nnf
