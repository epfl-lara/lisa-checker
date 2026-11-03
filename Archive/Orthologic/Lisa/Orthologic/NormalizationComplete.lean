import Lisa.Orthologic.Normalize
import Lisa.Orthologic.Reduced
import Lisa.Orthologic.Certificate

/-!
Prove the contradiction-reduced invariant of the executable normalizer. Cut
elimination then reduces every valid comparison to bounded-lattice containment,
which the structural comparator decides exactly.
-/

namespace Lisa.Orthologic.Nnf

variable {α : Type}

private theorem reduced_meetAll (ps : List (Nnf α))
    (hp : ∀ p ∈ ps, p.Reduced)
    (hn : ¬LatticeLe (meetAll ps) (meetAll ps).compl) : (meetAll ps).Reduced := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
      cases ps with
      | nil => exact hp p (by simp)
      | cons q qs =>
          change p.Reduced ∧ (meetAll (q :: qs)).Reduced ∧ _
          refine ⟨hp p (by simp), ih (fun r hr => hp r (List.mem_cons_of_mem p hr)) ?_, ?_⟩
          · intro h
            apply hn
            exact .injectRight (.projectRight h)
          · intro h
            exact False.elim (hn h)

private theorem reduced_meetFactors {p t : Nnf α} (hp : p.Reduced)
    (ht : t ∈ p.meetFactors) : t.Reduced := by
  induction p with
  | meet p q ih ik =>
      simp only [meetFactors, List.mem_append] at ht
      exact ht.elim (ih hp.1) (ik hp.2.1)
  | top => simp [meetFactors] at ht
  | _ => simp only [meetFactors, List.mem_singleton] at ht; subst t; exact hp

variable [DecidableEq α]

private theorem reduced_refineFactor (context : Nnf α) {p t : Nnf α}
    (hp : p.Reduced) (ht : t ∈ refineFactor context p) : t.Reduced := by
  induction p with
  | meet p q ih ik =>
      simp only [refineFactor, List.mem_append] at ht
      exact ht.elim (ih hp.1) (ik hp.2.1)
  | join p q ih ik =>
      rw [refineFactor] at ht
      split at ht
      · exact ih hp.1 ht
      · split at ht
        · exact ik hp.2.1 ht
        · simp only [List.mem_singleton] at ht; subst t; exact hp
  | top => simp [refineFactor] at ht
  | _ => simp only [refineFactor, List.mem_singleton] at ht; subst t; exact hp

private theorem mem_pruneFactors {accepted ps : List (Nnf α)} {t : Nnf α}
    (ht : t ∈ pruneFactors accepted ps) : t ∈ ps ++ accepted := by
  induction ps generalizing accepted with
  | nil => simpa [pruneFactors] using ht
  | cons p ps ih =>
      rw [pruneFactors] at ht
      split at ht
      · have := ih ht; simp_all
      · have := ih ht; simp_all [or_left_comm]

/-- Preserve reduced subterms while flattening, refining and pruning a meet. -/
theorem reduced_normalMeet (ps : List (Nnf α)) (hp : ∀ p ∈ ps, p.Reduced) :
    (normalMeet ps).Reduced := by
  unfold normalMeet
  dsimp only
  split
  · trivial
  · rename_i hn
    apply reduced_meetAll
    · intro t ht
      rw [List.mem_reverse] at ht
      have hm := mem_pruneFactors ht
      simp only [List.append_nil] at hm
      obtain ⟨p, hmem, ht⟩ := List.mem_flatMap.mp hm
      exact reduced_refineFactor _ (hp p hmem) ht
    · intro h
      exact hn (structuralLe_iff_lattice.mpr h)

theorem reduced_smartMeet {p q : Nnf α} (hp : p.Reduced) (hq : q.Reduced) :
    (smartMeet p q).Reduced := by
  apply reduced_normalMeet
  intro t ht
  simp only [List.mem_append] at ht
  exact ht.elim (reduced_meetFactors hp) (reduced_meetFactors hq)

theorem reduced_smartJoin {p q : Nnf α} (hp : p.Reduced) (hq : q.Reduced) :
    (smartJoin p q).Reduced := (reduced_smartMeet hp.compl hq.compl).compl

/-- Eliminate all contraction obligations throughout the normalized tree. -/
theorem reduced_normalize (p : Nnf α) : p.normalize.Reduced := by
  induction p with
  | lit a s => trivial
  | bot => trivial
  | top => trivial
  | meet p q ih ik => exact reduced_smartMeet ih ik
  | join p q ih ik => exact reduced_smartJoin ih ik

/-- Recognize every orthologic inequality by comparing its normalized operands. -/
theorem checkNormalizedLe_complete {p q : Nnf α} (h : Calculus.Derives p q) :
    checkNormalizedLe p q = true := by
  have ho := Orthogonal.complete p.normalize q.normalize.compl
    (fun _ _ v => by simpa using h.sound v)
  have hl := ho.lattice_of_reduced (reduced_normalize p) (reduced_normalize q).compl
  apply structuralLe_iff_lattice.mpr
  simpa only [compl_compl] using hl

/-- Decide orthologic derivability without a search or saturation fallback. -/
theorem checkNormalizedLe_iff (p q : Nnf α) :
    checkNormalizedLe p q = true ↔ Calculus.Derives p q :=
  ⟨fun h => Calculus.complete p q (fun _ _ v => checkNormalizedLe_sound v h),
    checkNormalizedLe_complete⟩

end Lisa.Orthologic.Nnf
