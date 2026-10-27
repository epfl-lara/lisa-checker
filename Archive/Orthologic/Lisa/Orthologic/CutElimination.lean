import Lisa.Orthologic.Calculus

namespace Lisa.Orthologic.Calculus

open Nnf

private theorem no_top_none {α : Type} (h : @Proof α false (some .top) none) : False := by
  have hf := h.sound (fun _ => (∅ : Set Unit))
  simp [Proof.evalPosition, Nnf.eval] at hf

/-- Delete a top position; it contributes nothing to an orthogonality sequent. -/
theorem eraseTop {α : Type} {g d} (h : @Proof α false g d) :
    (g = some .top → Nonempty (Proof false none d)) ∧
    (d = some .top → Nonempty (Proof false g none)) := by
  induction h with
  | ax p =>
    constructor
    · intro hp
      cases hp
      exact ⟨.swap (.bot _)⟩
    · intro hp
      cases p <;> simp_all [Nnf.compl]
      exact ⟨.bot _⟩
  | bot d =>
    constructor
    · simp
    · intro _; exact ⟨.bot _⟩
  | weaken h ih =>
    constructor
    · intro hg
      cases hg
      exact False.elim (no_top_none h)
    · intro _; exact ⟨h⟩
  | contract h ih =>
    constructor
    · intro hg
      cases hg
      obtain ⟨k⟩ := ih.2 rfl
      exact False.elim (no_top_none k)
    · simp
  | meetLeft h ih =>
    constructor
    · simp
    · intro hd
      obtain ⟨k⟩ := ih.2 hd
      exact ⟨.meetLeft k⟩
  | meetRight h ih =>
    constructor
    · simp
    · intro hd
      obtain ⟨k⟩ := ih.2 hd
      exact ⟨.meetRight k⟩
  | join h k ih ik =>
    constructor
    · simp
    · intro hd
      obtain ⟨h'⟩ := ih.2 hd
      obtain ⟨k'⟩ := ik.2 hd
      exact ⟨.join h' k'⟩
  | swap h ih => exact ⟨fun hg => (ih.2 hg).map Proof.swap,
      fun hd => (ih.1 hd).map Proof.swap⟩
  | cut h _ _ _ _ => cases h

/-- Break a commutation tie by moving a right-hand contraction to the left. -/
private def contractionPenalty {α : Type} {g d} : @Proof α false g d → Nat
  | .contract _ => 1
  | _ => 0

private theorem penalty_le_one {α : Type} {g d} (h : @Proof α false g d) :
    contractionPenalty h ≤ 1 := by
  cases h <;> simp [contractionPenalty]

set_option maxHeartbeats 2000000 in
private theorem eliminateCutBound {α : Type} (rank fuel : Nat) :
    ∀ (b c : Nnf α), c = b.compl → ∀ {g d},
    (A : Proof false g (some b)) → (B : Proof false (some c) d) →
    b.size < rank → 2 * (A.size + B.size) + contractionPenalty B < fuel →
    Nonempty (Proof false g d) := by
  revert fuel
  induction rank using Nat.strong_induction_on with | h rank outer =>
  intro fuel
  induction fuel using Nat.strong_induction_on with | h fuel inner =>
  intro b c hc g d inputA inputB hr hf
  have recur (b' c' : Nnf α) (hc' : c' = b'.compl) {g' d'}
      (A' : Proof false g' (some b')) (B' : Proof false (some c') d')
      (decrease : b'.size < b.size ∨
        (b'.size < rank ∧ 2 * (A'.size + B'.size) + contractionPenalty B' + 1 < fuel) := by
          first
          | left; simp_all only [Nnf.size_compl, Nnf.size, Nnf.compl]; omega
          | right; constructor
            · simp_all only [Nnf.size_compl, Nnf.size, Nnf.compl]
            · simp_all only [Nnf.size_compl, Nnf.size, Nnf.compl, Proof.size,
                contractionPenalty]; omega) :
      Nonempty (Proof false g' d') := by
    rcases decrease with smaller | ⟨hr', hf'⟩
    · exact outer (b'.size + 1) (by omega)
        (2 * (A'.size + B'.size) + contractionPenalty B' + 1)
        b' c' hc' A' B' (by omega) (by omega)
    · exact inner (2 * (A'.size + B'.size) + contractionPenalty B' + 1)
        hf' b' c' hc' A' B' hr' (by omega)
  cases hA : inputA with
  | ax p =>
    subst c
    simpa using (show Nonempty _ from ⟨inputB⟩)
  | bot d => exact ⟨.bot _⟩
  | weaken A => exact ⟨.weaken A⟩
  | meetLeft A =>
    obtain ⟨P⟩ := recur b c hc A inputB
    exact ⟨.meetLeft P⟩
  | meetRight A =>
    obtain ⟨P⟩ := recur b c hc A inputB
    exact ⟨.meetRight P⟩
  | join A C =>
    obtain ⟨P⟩ := recur b c hc A inputB
    obtain ⟨Q⟩ := recur b c hc C inputB
    exact ⟨.join P Q⟩
  | swap A =>
    cases hB : inputB with
    | ax p =>
      subst c
      simpa using (show Nonempty _ from ⟨A.swap⟩)
    | bot d =>
      have hb : b = .top := by
        have := congrArg Nnf.compl hc
        simpa [Nnf.compl] using this.symm
      subst b
      obtain ⟨P⟩ := (eraseTop A).1 rfl
      exact ⟨.weaken P.swap⟩
    | weaken B =>
      obtain ⟨P⟩ := recur b c hc A.swap B (by
        right
        constructor
        · exact hr
        · have := penalty_le_one B
          simp_all only [Proof.size, contractionPenalty]
          omega)
      exact ⟨.weaken P⟩
    | swap B =>
      obtain ⟨P⟩ := recur c b (by rw [hc, Nnf.compl_compl]) B A (by
        right
        constructor
        · simpa only [hc, Nnf.size_compl] using hr
        · have := penalty_le_one A
          simp_all only [Proof.size, contractionPenalty]
          omega)
      exact ⟨P.swap⟩
    | cut h _ _ => cases h
    | contract B =>
      cases hC : A with
      | ax p =>
        subst c
        simpa using (show Nonempty _ from ⟨B.contract⟩)
      | bot d =>
        have hc' : c = .top := by simpa [Nnf.compl] using hc
        subst c
        exact False.elim (no_top_none B.contract)
      | weaken C =>
        subst c
        exact False.elim (no_empty
          (.cut rfl C.withCuts.swap B.withCuts.contract))
      | contract C =>
        subst c
        exact False.elim (no_empty
          (.cut rfl C.withCuts.contract.swap B.withCuts.contract))
      | meetLeft C =>
        obtain ⟨P⟩ := recur c _ (by rw [hc, Nnf.compl_compl]) B.contract.swap C.meetLeft
        exact ⟨P.swap⟩
      | meetRight C =>
        obtain ⟨P⟩ := recur c _ (by rw [hc, Nnf.compl_compl]) B.contract.swap C.meetRight
        exact ⟨P.swap⟩
      | join C D =>
        obtain ⟨P⟩ := recur c _ (by rw [hc, Nnf.compl_compl]) B.contract.swap (C.join D)
        exact ⟨P.swap⟩
      | swap C => exact recur b c hc C B.contract
      | cut h _ _ => cases h
    | @meetLeft p q _ B =>
      have hb : b = .join p.compl q.compl := by
        simpa [Nnf.compl] using (congrArg Nnf.compl hc).symm
      subst b
      cases hC : A with
      | ax p => simpa [Nnf.compl] using (show Nonempty _ from ⟨B.meetLeft⟩)
      | weaken C =>
        obtain ⟨P⟩ := recur (.join p.compl q.compl) (.meet p q)
          (by simp [Nnf.compl]) C.swap B.meetLeft
        exact ⟨.swap (.weaken P.swap)⟩
      | swap C =>
        exact recur (.join p.compl q.compl) (.meet p q)
          (by simp [Nnf.compl]) C B.meetLeft
      | join C D => exact recur p.compl p (by simp) C.swap B
      | contract C =>
        cases hD : C with
        | weaken D =>
          exact recur (.join p.compl q.compl) (.meet p q)
            (by simp [Nnf.compl]) D.swap B.meetLeft
        | swap D =>
          exact recur (.join p.compl q.compl) (.meet p q)
            (by simp [Nnf.compl]) D.contract.swap B.meetLeft
        | join D E =>
          obtain ⟨P⟩ := recur (.join p.compl q.compl) (.meet p q)
            (by simp [Nnf.compl]) D B.meetLeft
          obtain ⟨Q⟩ := recur p.compl p (by simp) P.swap B
          exact ⟨Q.contract.swap⟩
        | cut h _ _ => cases h
      | cut h _ _ => cases h
    | @meetRight p q _ B =>
      have hb : b = .join p.compl q.compl := by
        simpa [Nnf.compl] using (congrArg Nnf.compl hc).symm
      subst b
      cases hC : A with
      | ax p => simpa [Nnf.compl] using (show Nonempty _ from ⟨B.meetRight⟩)
      | weaken C =>
        obtain ⟨P⟩ := recur (.join p.compl q.compl) (.meet p q)
          (by simp [Nnf.compl]) C.swap B.meetRight
        exact ⟨.swap (.weaken P.swap)⟩
      | swap C =>
        exact recur (.join p.compl q.compl) (.meet p q)
          (by simp [Nnf.compl]) C B.meetRight
      | join C D => exact recur q.compl q (by simp) D.swap B
      | contract C =>
        cases hD : C with
        | weaken D =>
          exact recur (.join p.compl q.compl) (.meet p q)
            (by simp [Nnf.compl]) D.swap B.meetRight
        | swap D =>
          exact recur (.join p.compl q.compl) (.meet p q)
            (by simp [Nnf.compl]) D.contract.swap B.meetRight
        | join D E =>
          obtain ⟨P⟩ := recur (.join p.compl q.compl) (.meet p q)
            (by simp [Nnf.compl]) E B.meetRight
          obtain ⟨Q⟩ := recur q.compl q (by simp) P.swap B
          exact ⟨Q.contract.swap⟩
        | cut h _ _ => cases h
      | cut h _ _ => cases h
    | @join p q _ B C =>
      have hb : b = .meet p.compl q.compl := by
        simpa [Nnf.compl] using (congrArg Nnf.compl hc).symm
      subst b
      cases hD : A with
      | ax p => simpa [Nnf.compl] using (show Nonempty _ from ⟨B.join C⟩)
      | weaken D =>
        obtain ⟨P⟩ := recur (.meet p.compl q.compl) (.join p q)
          (by simp [Nnf.compl]) D.swap (B.join C)
        exact ⟨.swap (.weaken P.swap)⟩
      | swap D =>
        exact recur (.meet p.compl q.compl) (.join p q)
          (by simp [Nnf.compl]) D (B.join C)
      | meetLeft D => exact recur p.compl p (by simp) D.swap B
      | meetRight D => exact recur q.compl q (by simp) D.swap C
      | contract D =>
        cases hE : D with
        | weaken E =>
          exact recur (.meet p.compl q.compl) (.join p q)
            (by simp [Nnf.compl]) E.swap (B.join C)
        | swap E =>
          exact recur (.meet p.compl q.compl) (.join p q)
            (by simp [Nnf.compl]) E.contract.swap (B.join C)
        | meetLeft E =>
          obtain ⟨P⟩ := recur (.meet p.compl q.compl) (.join p q)
            (by simp [Nnf.compl]) E (B.join C)
          obtain ⟨Q⟩ := recur p.compl p (by simp) P.swap B
          exact ⟨Q.contract.swap⟩
        | meetRight E =>
          obtain ⟨P⟩ := recur (.meet p.compl q.compl) (.join p q)
            (by simp [Nnf.compl]) E (B.join C)
          obtain ⟨Q⟩ := recur q.compl q (by simp) P.swap C
          exact ⟨Q.contract.swap⟩
        | cut h _ _ => cases h
      | cut h _ _ => cases h
  | cut h _ _ => cases h

/-- Eliminate one cut between two cut-free derivations. -/
theorem eliminateCut {α : Type} (b : Nnf α) {g d}
    (A : Proof false g (some b)) (B : Proof false (some b.compl) d) :
    Nonempty (Proof false g d) :=
  eliminateCutBound (b.size + 1)
    (2 * (A.size + B.size) + contractionPenalty B + 1)
    b b.compl rfl A B (by omega) (by omega)

/-- Remove all cuts, starting with cut-free translations of the premises. -/
theorem cutFree {α : Type} {g d} (h : @Proof α true g d) :
    Nonempty (Proof false g d) := by
  induction h with
  | ax p => exact ⟨.ax p⟩
  | bot d => exact ⟨.bot d⟩
  | weaken h ih => exact ih.map Proof.weaken
  | contract h ih => exact ih.map Proof.contract
  | meetLeft h ih => exact ih.map Proof.meetLeft
  | meetRight h ih => exact ih.map Proof.meetRight
  | join h k ih ik =>
    obtain ⟨h'⟩ := ih
    obtain ⟨k'⟩ := ik
    exact ⟨.join h' k'⟩
  | swap h ih => exact ih.map Proof.swap
  | cut _ h k ih ik =>
    obtain ⟨h'⟩ := ih
    obtain ⟨k'⟩ := ik
    exact eliminateCut _ h' k'

/-- Derive every universally valid inequality without cut. -/
theorem complete_cutFree {α : Type} (p q : Nnf α)
    (h : ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ q.eval v) :
    Nonempty (Proof false (some p) (some q.compl)) := by
  obtain ⟨h'⟩ := complete p q h
  exact cutFree h'

end Lisa.Orthologic.Calculus
