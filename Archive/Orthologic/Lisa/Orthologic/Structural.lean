import Lisa.Orthologic.LatticeContainment

/-!
Decide bounded-lattice containment by structural traversal. On contradiction-
reduced inputs, this also decides orthologic containment; see
`NormalizationComplete` for the invariant and completeness theorem.

Reference: `lattices_leq` in Simon Guilloud's `orthologic-coq/src/ol.ml`.
-/

namespace Lisa.Orthologic.Nnf

variable {α : Type} [DecidableEq α]

/-- Retain the chosen flattening direction in recursive comparison queries. -/
inductive ComparisonSide where
  | both | project | inject
  deriving DecidableEq, Hashable

-- Commit to one side while flattening a meet/join comparison. Otherwise the
-- binary representation revisits pairs through every interleaving of the sides.
/-- Compare two trees without revisiting meet/join interleavings. -/
def structuralCompare (side : ComparisonSide) (p q : Nnf α) : Bool :=
  if p = q then true
  else match side, p, q with
    | .project, .meet a b, q =>
        structuralCompare .project a q || structuralCompare .project b q
    | .inject, p, .join a b =>
        structuralCompare .inject p a || structuralCompare .inject p b
    | _, .bot, _ => true
    | _, _, .top => true
    | _, p, .meet a b => structuralCompare .both p a && structuralCompare .both p b
    | _, .join a b, q => structuralCompare .both a q && structuralCompare .both b q
    | .both, .meet a b, .join c d =>
        structuralCompare .project a (.join c d) || structuralCompare .project b (.join c d) ||
        structuralCompare .inject (.meet a b) c || structuralCompare .inject (.meet a b) d
    | _, .meet a b, q => structuralCompare .both a q || structuralCompare .both b q
    | _, p, .join a b => structuralCompare .both p a || structuralCompare .both p b
    | _, _, _ => false
termination_by p.size + q.size
decreasing_by all_goals simp_all only [size]; omega

/-- Recognize lattice containment by descending into the two input trees. -/
def structuralLe (p q : Nnf α) : Bool := structuralCompare .both p q

private theorem from_meet_left {L : Type} [Lattice L] {a b c : L}
    (h : a ≤ c) : a ⊓ b ≤ c := inf_le_left.trans h

private theorem from_meet_right {L : Type} [Lattice L] {a b c : L}
    (h : b ≤ c) : a ⊓ b ≤ c := inf_le_right.trans h

private theorem to_join_left {L : Type} [Lattice L] {a b c : L}
    (h : a ≤ b) : a ≤ b ⊔ c := h.trans le_sup_left

private theorem to_join_right {L : Type} [Lattice L] {a b c : L}
    (h : a ≤ c) : a ≤ b ⊔ c := h.trans le_sup_right

private theorem structuralCompare_sound {L : Type} [Ortholattice L]
    (v : α → L) {side : ComparisonSide} {p q : Nnf α}
    (h : structuralCompare side p q = true) :
    p.eval v ≤ q.eval v := by
  fun_induction structuralCompare side p q
  all_goals simp_all only [Bool.and_eq_true, Bool.or_eq_true, Bool.false_eq_true, eval]
  all_goals
    aesop (add safe [le_rfl, bot_le, le_top, le_inf, sup_le])
      (add unsafe [from_meet_left, from_meet_right, to_join_left, to_join_right])

theorem structuralLe_sound {L : Type} [Ortholattice L]
    (v : α → L) {p q : Nnf α} (h : structuralLe p q = true) :
    p.eval v ≤ q.eval v := structuralCompare_sound v h

private theorem structuralCompare_lattice {side : ComparisonSide} {p q : Nnf α}
    (h : structuralCompare side p q = true) : LatticeLe p q := by
  fun_induction structuralCompare side p q
  all_goals simp_all only [Bool.and_eq_true, Bool.or_eq_true, Bool.false_eq_true]
  all_goals aesop (add safe [LatticeLe.refl, LatticeLe.bot, LatticeLe.top,
    LatticeLe.meet, LatticeLe.join]) (add unsafe [LatticeLe.projectLeft,
    LatticeLe.projectRight, LatticeLe.injectLeft, LatticeLe.injectRight])

private theorem project_leaf (p c d : Nnf α)
    (h : ∃ t ∈ LatticeLe.meetLeaves p,
      structuralCompare .both t (.join c d) = true) :
    structuralCompare .project p (.join c d) = true := by
  induction p with
  | meet p q ih ik =>
      rw [structuralCompare.eq_def]
      split
      · rfl
      · change (structuralCompare .project p (.join c d) ||
          structuralCompare .project q (.join c d)) = true
        simp only [LatticeLe.meetLeaves, List.mem_append] at h
        rcases h with ⟨t, ht | ht, h⟩
        · exact Bool.or_eq_true_iff.mpr (Or.inl (ih ⟨t, ht, h⟩))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (ik ⟨t, ht, h⟩))
  | _ =>
      obtain ⟨t, ht, h⟩ := h
      simp only [LatticeLe.meetLeaves, List.mem_singleton] at ht
      subst t
      rw [structuralCompare.eq_def] at h ⊢
      exact h

private theorem inject_leaf (a b q : Nnf α)
    (h : ∃ t ∈ LatticeLe.joinLeaves q,
      structuralCompare .both (.meet a b) t = true) :
    structuralCompare .inject (.meet a b) q = true := by
  induction q with
  | join p q ih ik =>
      rw [structuralCompare.eq_def]
      split
      · rfl
      · change (structuralCompare .inject (.meet a b) p ||
          structuralCompare .inject (.meet a b) q) = true
        simp only [LatticeLe.joinLeaves, List.mem_append] at h
        rcases h with ⟨t, ht | ht, h⟩
        · exact Bool.or_eq_true_iff.mpr (Or.inl (ih ⟨t, ht, h⟩))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (ik ⟨t, ht, h⟩))
  | _ =>
      obtain ⟨t, ht, h⟩ := h
      simp only [LatticeLe.joinLeaves, List.mem_singleton] at ht
      subst t
      rw [structuralCompare.eq_def] at h ⊢
      exact h

private theorem structuralCompare_complete {p q : Nnf α} (h : LatticeLe p q) :
    structuralCompare .both p q = true := by
  rw [structuralCompare.eq_def]
  split
  · rfl
  · cases q with
    | top => cases p <;> rfl
    | meet q r =>
        cases p with
        | bot => rfl
        | _ =>
            exact Bool.and_eq_true_iff.mpr ⟨structuralCompare_complete h.to_meet.1,
              structuralCompare_complete h.to_meet.2⟩
    | bot =>
        cases p with
        | bot => rfl
        | join p r =>
            exact Bool.and_eq_true_iff.mpr ⟨structuralCompare_complete h.of_join.1,
              structuralCompare_complete h.of_join.2⟩
        | meet p r =>
            cases h with
            | projectLeft h =>
                exact Bool.or_eq_true_iff.mpr (Or.inl (structuralCompare_complete h))
            | projectRight h =>
                exact Bool.or_eq_true_iff.mpr (Or.inr (structuralCompare_complete h))
        | lit a s => cases h
        | top => cases h
    | lit a s =>
        cases p with
        | bot => rfl
        | join p r =>
            exact Bool.and_eq_true_iff.mpr ⟨structuralCompare_complete h.of_join.1,
              structuralCompare_complete h.of_join.2⟩
        | meet p r =>
            cases h with
            | projectLeft h =>
                exact Bool.or_eq_true_iff.mpr (Or.inl (structuralCompare_complete h))
            | projectRight h =>
                exact Bool.or_eq_true_iff.mpr (Or.inr (structuralCompare_complete h))
        | lit b t => cases h; contradiction
        | top => cases h
    | join c d =>
        cases p with
        | bot => rfl
        | join p r =>
            exact Bool.and_eq_true_iff.mpr ⟨structuralCompare_complete h.of_join.1,
              structuralCompare_complete h.of_join.2⟩
        | meet a b =>
            rcases h.whitman with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
            · simp only [LatticeLe.meetLeaves, List.mem_append] at ht
              rcases ht with ht | ht
              · have hs := LatticeLe.size_meetLeaves ht
                have hc := project_leaf a c d ⟨t, ht, structuralCompare_complete h⟩
                simp only [Bool.or_eq_true]; exact Or.inl (Or.inl (Or.inl hc))
              · have hs := LatticeLe.size_meetLeaves ht
                have hc := project_leaf b c d ⟨t, ht, structuralCompare_complete h⟩
                simp only [Bool.or_eq_true]; exact Or.inl (Or.inl (Or.inr hc))
            · simp only [LatticeLe.joinLeaves, List.mem_append] at ht
              rcases ht with ht | ht
              · have hs := LatticeLe.size_joinLeaves ht
                have hc := inject_leaf a b c ⟨t, ht, structuralCompare_complete h⟩
                simp only [Bool.or_eq_true]; exact Or.inl (Or.inr hc)
              · have hs := LatticeLe.size_joinLeaves ht
                have hc := inject_leaf a b d ⟨t, ht, structuralCompare_complete h⟩
                simp only [Bool.or_eq_true]; exact Or.inr hc
        | lit a s =>
            cases h with
            | injectLeft h =>
                exact Bool.or_eq_true_iff.mpr (Or.inl (structuralCompare_complete h))
            | injectRight h =>
                exact Bool.or_eq_true_iff.mpr (Or.inr (structuralCompare_complete h))
        | top =>
            cases h with
            | injectLeft h =>
                exact Bool.or_eq_true_iff.mpr (Or.inl (structuralCompare_complete h))
            | injectRight h =>
                exact Bool.or_eq_true_iff.mpr (Or.inr (structuralCompare_complete h))
termination_by p.size + q.size
decreasing_by
  all_goals
    simp_all only [heq_eq_eq, Nnf.meet.injEq, Nnf.join.injEq]
    subst_vars
    simp_all only [size]
    omega

/-- Decide precisely the cut-free bounded-lattice containment relation. -/
theorem structuralLe_iff_lattice {p q : Nnf α} :
    structuralLe p q = true ↔ LatticeLe p q :=
  ⟨structuralCompare_lattice, structuralCompare_complete⟩

end Lisa.Orthologic.Nnf
