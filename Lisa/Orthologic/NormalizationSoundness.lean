import Lisa.Orthologic.Normalization
import Lisa.Orthologic.ComparisonSoundness

/-! Every normalization step preserves contextual equivalence in Ordered.
The refinement invariant records both strengthening of a factor and preservation
of all consequences needed from the original surrounding conjunction.
-/

namespace Lisa.Orthologic
open SimpleExpr

namespace ProvableLE

theorem conj_subset {ps qs : List (SimpleExpr prop)} (h : ∀ p ∈ ps, p ∈ qs) :
    ProvableLE (.conj qs) (.conj ps) :=
  conj_right ps (fun p hp => conj_member qs (h p hp))

end ProvableLE

namespace ProvableEQ

theorem conj_members {ps qs : List (SimpleExpr prop)} (h : ∀ p, p ∈ ps ↔ p ∈ qs) :
    ProvableEQ (.conj ps) (.conj qs) :=
  of_le (ProvableLE.conj_subset (fun p hp => (h p).mpr hp))
    (ProvableLE.conj_subset (fun p hp => (h p).mp hp))

theorem conj_singleton (p : SimpleExpr prop) : ProvableEQ (.conj [p]) p :=
  of_le (ProvableLE.conj_member _ (by simp)) (ProvableLE.conj_right _ (by simpa using ProvableLE.refl p))

theorem conj_empty : ProvableEQ (.conj []) .top :=
  of_le (ProvableLE.top _) (ProvableLE.conj_right _ (by simp))

theorem conj_map (ps : List (SimpleExpr prop)) (f : SimpleExpr prop → SimpleExpr prop)
    (h : ∀ p ∈ ps, ProvableEQ (f p) p) : ProvableEQ (.conj (ps.map f)) (.conj ps) := by
  apply of_le
  · apply ProvableLE.conj_right
    intro p hp
    exact (ProvableLE.conj_member _ (List.mem_map.mpr ⟨p, hp, rfl⟩)).trans (h p hp).le
  · apply ProvableLE.conj_right
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (ProvableLE.conj_member _ hp).trans (h p hp).symm.le

end ProvableEQ

theorem inverse_sound (p : SimpleExpr prop) : ProvableEQ (inverse p) (.neg p) := by
  unfold inverse
  split
  · exact ProvableEQ.of_le (ProvableLE.doubleNegIntro _) (ProvableLE.doubleNegElim _)
  · exact ProvableEQ.refl _

/-- Refinement strengthens a factor, but only by consequences of the original
context. This invariant is enough to preserve the whole conjunction. -/
theorem refineFactor_sound (context : SimpleExpr prop) (positive : Bool)
    (p : SimpleExpr prop) (sign : Bool) :
    ProvableLE (.conj (refineFactor context positive p sign)) (polar p sign) ∧
    (ProvableLE context (polar p sign) →
      ProvableLE context (.conj (refineFactor context positive p sign))) := by
  unfold refineFactor
  split
  case h_1 =>
    obtain ⟨d, e⟩ := refineFactor_sound context positive _ (!sign)
    exact ⟨d.trans (polar_neg _ _).symm.le, fun h => e (h.trans (polar_neg _ _).le)⟩
  case h_2 =>
    rename_i ps
    constructor
    · apply ProvableLE.conj_right
      intro q hq
      have sub : ProvableLE (.conj (ps.attach.flatMap fun p => refineFactor context positive p.val true))
          (.conj (refineFactor context positive q true)) :=
        ProvableLE.conj_subset (fun r hr => List.mem_flatMap.mpr ⟨⟨q, hq⟩, List.mem_attach _ _, hr⟩)
      exact sub.trans (refineFactor_sound context positive q true).1
    · intro h
      apply ProvableLE.conj_right
      intro r hr
      obtain ⟨q, _, hr⟩ := List.mem_flatMap.mp hr
      exact ((refineFactor_sound context positive q.val true).2
        (h.trans (ProvableLE.conj_member _ q.property))).trans (ProvableLE.conj_member _ hr)
  case h_3 =>
    rename_i ps
    split
    · rename_i q hq
      obtain ⟨d, e⟩ := refineFactor_sound context positive q.val false
      have hc : ProvableLE context (.neg q.val) := by
        have h := List.find?_some hq
        cases positive
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (ProvableLE.doubleNegIntro context).trans (polarLEQ_sound _ _ _ _ h).neg
        · simp only [↓reduceIte] at h
          exact polarLEQ_sound _ _ _ _ h
      exact ⟨d.trans (ProvableLE.conj_member _ q.property).neg, fun _ => e hc⟩
    · exact ⟨(ProvableEQ.conj_singleton _).le, fun h => h.trans (ProvableEQ.conj_singleton _).symm.le⟩
  case h_4 =>
    exact ⟨(ProvableEQ.conj_singleton _).le, fun h => h.trans (ProvableEQ.conj_singleton _).symm.le⟩
termination_by p.size
decreasing_by
  all_goals try subst_vars
  all_goals try simp only [SimpleExpr.size]
  all_goals try first
    | omega
    | simpa only [SimpleExpr.size] using size_lt_conj hq
    | simpa only [SimpleExpr.size] using size_lt_conj q.property
  all_goals
    rename_i ps u _ _ _
    simpa only [SimpleExpr.size] using size_lt_conj u.property

theorem pruneFactors_sound (accepted remaining : List (SimpleExpr prop)) :
    ProvableEQ (.conj (pruneFactors accepted remaining)) (.conj (remaining ++ accepted)) := by
  induction remaining generalizing accepted with
  | nil => exact ProvableEQ.refl _
  | cons p ps ih =>
      unfold pruneFactors
      split
      · rename_i h
        apply (ih accepted).trans
        apply ProvableEQ.of_le
        · apply ProvableLE.conj_right
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact latticesLEQ_sound h
          · exact ProvableLE.conj_member _ hq
        · exact ProvableLE.conj_subset (fun q hq => List.mem_cons_of_mem p hq)
      · apply (ih (p :: accepted)).trans
        apply ProvableEQ.conj_members
        intro q; simp [or_left_comm]

theorem refineList_sound (ps : List (SimpleExpr prop)) (positive : Bool) :
    ProvableEQ
      (.conj (ps.foldl (fun acc p => refineFactor (.conj ps) positive p true ++ acc) []))
      (.conj ps) := by
  have members (xs acc : List (SimpleExpr prop)) (q : SimpleExpr prop) :
      q ∈ xs.foldl (fun acc p => refineFactor (.conj ps) positive p true ++ acc) acc ↔
        q ∈ acc ∨ ∃ p ∈ xs, q ∈ refineFactor (.conj ps) positive p true := by
    induction xs generalizing acc with
    | nil => simp
    | cons p xs ih => simp only [List.foldl_cons, ih, List.mem_append, List.mem_cons]
                      aesop
  apply ProvableEQ.of_le
  · apply ProvableLE.conj_right
    intro p hp
    have sub : ProvableLE
        (.conj (ps.foldl (fun acc p => refineFactor (.conj ps) positive p true ++ acc) []))
        (.conj (refineFactor (.conj ps) positive p true)) := by
      apply ProvableLE.conj_subset
      intro q hq
      exact (members ps [] q).mpr (Or.inr ⟨p, hp, hq⟩)
    exact sub.trans (refineFactor_sound (.conj ps) positive p true).1
  · apply ProvableLE.conj_right
    intro q hq
    obtain hq | ⟨p, hp, hq⟩ := (members ps [] q).mp hq
    · simp at hq
    · exact ((refineFactor_sound (.conj ps) positive p true).2
        (ProvableLE.conj_member _ hp)).trans (ProvableLE.conj_member _ hq)

theorem reduceList_sound (ps : List (SimpleExpr prop)) (positive : Bool) :
    ProvableEQ (.conj (reduceList ps positive)) (.conj ps) := by
  unfold reduceList
  exact (pruneFactors_sound _ _).trans (by simpa using refineList_sound ps positive)

theorem assemble_sound (ps : List (SimpleExpr prop)) (positive : Bool) :
    ProvableEQ (assemble ps positive) (polar (.conj ps) positive) := by
  have h : ProvableEQ (match ps with | [] => .top | [p] => p | ps => .conj ps) (.conj ps) := by
    cases ps with
    | nil => exact ProvableEQ.conj_empty.symm
    | cons p ps => cases ps with
      | nil => exact (ProvableEQ.conj_singleton p).symm
      | cons q qs => exact ProvableEQ.refl _
  cases positive
  · exact (inverse_sound _).trans h.neg
  · exact h

theorem contradiction_sound (ps : List (SimpleExpr prop)) (positive : Bool)
    (h : checkForContradiction ps positive = true) : ProvableLE (.conj ps) (.neg .top) := by
  have hn : ProvableLE (.conj ps) (.neg (.conj ps)) := by
    unfold checkForContradiction at h
    cases positive
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
      exact (ProvableLE.conj_member _ hp).trans (polarLEQ_sound _ _ _ _ h)
    · simp only [↓reduceIte] at h
      obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
      exact (polarLEQ_sound _ _ _ _ h).trans (ProvableLE.conj_member _ hp).neg
  intro ρ
  obtain ⟨d⟩ := hn ρ
  have hsort := (SimpleExpr.conj ps).reify_sort ρ
  have result := Derivation.contradiction hsort (by simpa using d)
  simpa using Nonempty.intro (Derivation.trans hsort (show isFormula Expr.bot from rfl)
    (isFormula_neg (show isFormula Expr.top from rfl)) result
    (Derivation.bot_le (isFormula_neg (show isFormula Expr.top from rfl))))

theorem reduce_sound (ps : List (SimpleExpr prop)) (positive : Bool) :
    ProvableEQ (reduce ps positive) (polar (.conj ps) positive) := by
  unfold reduce
  dsimp only
  split
  · rename_i h
    have hb := ProvableEQ.of_le (contradiction_sound _ _ h) (ProvableLE.bot _)
    have he := (reduceList_sound ps positive).polar positive
    cases positive
    · apply ProvableEQ.trans _ he
      exact (ProvableEQ.of_le (ProvableLE.doubleNegIntro .top) (ProvableLE.doubleNegElim .top)).trans hb.symm.neg
    · exact hb.symm.trans he
  · exact (assemble_sound _ _).trans ((reduceList_sound ps positive).polar positive)

theorem normalizeEquality_sound (a b : SimpleExpr ind) :
    ProvableEQ (normalizeEquality a b) (.equal a b) := by
  unfold normalizeEquality
  split
  · rename_i h
    apply ProvableEQ.of_le _ (ProvableLE.top _)
    intro ρ
    obtain ⟨d⟩ := ContextEq.individual (a.reify_sort _) (b.reify_sort _) (latticesEQ_sound a b h ρ)
    simpa using Nonempty.intro (Derivation.fromTheorem (show isFormula Expr.top from rfl)
      (isFormula_eq (a.reify_sort _) (b.reify_sort _)) d)
  · unfold orientEquality
    split
    · exact ProvableEQ.refl _
    · exact ProvableEQ.equal_symm _ _

theorem normalizeAll_sound (p : SimpleExpr prop) : ProvableEQ (normalizeAll p) (.all p) := by
  unfold normalizeAll
  split
  · apply ProvableEQ.of_le _ (ProvableLE.top _)
    intro ρ
    let x := ρ.fresh (SimpleExpr.top.toTerm.freeVars) ind
    have hx := ρ.fresh_not_mem (SimpleExpr.top.toTerm.freeVars) ind
    have hu := ρ.fresh_not_used (SimpleExpr.top.toTerm.freeVars) ind
    have hc := SimpleExpr.reify_all_at .top ρ x rfl hx hu
    have d := Derivation.forall_theorem x rfl (show isFormula Expr.top from rfl) Ordered.ProofTree.rightTrue
    have de := Derivation.fromTheorem (show isFormula Expr.top from rfl)
      (isFormula_forall rfl (show isFormula Expr.top from rfl)) d
    exact ⟨Derivation.convert (show isFormula Expr.top from rfl)
      (isFormula_forall rfl (show isFormula Expr.top from rfl)) (by simp)
      (by simpa using hc.symm) (by simpa using de)⟩
  · apply ProvableEQ.of_le (ProvableLE.bot _) _
    intro ρ
    let p := SimpleExpr.neg .top
    let x := ρ.fresh p.toTerm.freeVars ind
    have hx := ρ.fresh_not_mem p.toTerm.freeVars ind
    have hu := ρ.fresh_not_used p.toTerm.freeVars ind
    have hc := SimpleExpr.reify_all_at p ρ x rfl hx hu
    have hp : isFormula (Expr.neg Expr.top) := isFormula_neg rfl
    have d := Derivation.forall_elim x rfl hp
    exact ⟨Derivation.convert (isFormula_forall rfl hp) hp
      (by simpa [p] using hc.symm) (by simp)
      (by simpa [p] using d)⟩
  · exact ProvableEQ.refl _

/-- Every local rewrite and every recursive child normalization preserves
contextual equivalence, including at higher-order sorts. -/
private theorem normalForm_sound_size (n : Nat) :
    ∀ {s} (p : SimpleExpr s), p.size = n → ProvableEQ (computeNormalForm p) p := by
  induction n using Nat.strong_induction_on with | h n ih =>
  intro s p hn
  have child {s} (p : SimpleExpr s) (lt : p.size < n) := ih _ lt p rfl
  unfold computeNormalForm
  split
  case h_1 => exact ProvableEQ.refl _
  case h_2 => exact ProvableEQ.refl _
  case h_3 => exact ProvableEQ.refl _
  case h_4 =>
    exact ProvableEQ.app (child _ (by simp only [SimpleExpr.size] at hn; omega))
      (child _ (by simp only [SimpleExpr.size] at hn; omega))
  case h_5 => exact ProvableEQ.lam _ (child _ (by simp only [SimpleExpr.size] at hn; omega))
  case h_6 => exact ProvableEQ.refl _
  case h_7 =>
    apply (reduce_sound _ true).trans
    simp only [polar, ↓reduceIte, List.attach_map_val]
    apply ProvableEQ.conj_map
    intro q hq
    exact child q (by have := size_lt_conj hq; omega)
  case h_8 =>
    apply (reduce_sound _ false).trans
    simp only [polar, Bool.false_eq_true, ↓reduceIte, List.attach_map_val]
    apply ProvableEQ.neg
    apply ProvableEQ.conj_map
    intro q hq
    exact child q (by have := size_lt_conj hq; simp only [SimpleExpr.size] at hn this; omega)
  case h_9 =>
    exact (inverse_sound _).trans (child _ (by simp only [SimpleExpr.size] at hn; omega)).neg
  case h_10 =>
    exact (normalizeAll_sound _).trans (child _ (by simp only [SimpleExpr.size] at hn; omega)).all
  case h_11 =>
    exact (normalizeEquality_sound _ _).trans
      (ProvableEQ.equal (child _ (by simp only [SimpleExpr.size] at hn; omega))
        (child _ (by simp only [SimpleExpr.size] at hn; omega)))

theorem computeNormalForm_sound (p : SimpleExpr s) : ProvableEQ (computeNormalForm p) p :=
  normalForm_sound_size _ p rfl

theorem normalizedLEQ_sound {p q : SimpleExpr prop}
    (h : latticesLEQ (computeNormalForm p) (computeNormalForm q) = true) : ProvableLE p q :=
  (computeNormalForm_sound p).symm.le.trans
    ((latticesLEQ_sound h).trans (computeNormalForm_sound q).le)

theorem normalizedEQ_sound {p q : SimpleExpr s}
    (h : latticesEQ (computeNormalForm p) (computeNormalForm q) = true) : ProvableEQ p q :=
  (computeNormalForm_sound p).symm.trans
    ((latticesEQ_sound _ _ h).trans (computeNormalForm_sound q))

end Lisa.Orthologic
