import Lisa.Orthologic.Provability
import Lisa.Orthologic.Comparison

/-! Soundness of the mutually recursive comparisons in `Ordered AlphaBetaEta`.
The joint induction uses the same measure as the executable definitions.
-/

namespace Lisa.Orthologic
open SimpleExpr

theorem ProvableEQ.withPolarity {p q : SimpleExpr prop} (h : ProvableEQ p q) (s : Bool) :
    ProvableEQ (withPolarity p s) (withPolarity q s) := by cases s <;> first | exact h | exact h.neg

theorem withPolarity_neg (p : SimpleExpr prop) (s : Bool) :
    ProvableEQ (withPolarity (.neg p) s) (withPolarity p (!s)) := by
  cases s
  · exact ProvableEQ.of_le (ProvableLE.doubleNegElim p) (ProvableLE.doubleNegIntro p)
  · exact ProvableEQ.refl _

local macro "decrease" hn:ident : tactic => `(tactic|
  (try simp only [SimpleExpr.size] at $hn ⊢
   omega))

/-- Prove the two comparisons together. The extra unit for equivalence allows
its calls to implication at the same expression size. -/
private theorem comparison_sound (n : Nat) :
    (∀ p s q t, 2 * (p.size + q.size) = n → polarLEQ p s q t = true →
      ProvableLE (withPolarity p s) (withPolarity q t)) ∧
    (∀ {s : LSort} (p q : SimpleExpr s), 2 * (p.size + q.size) + 1 = n →
      latticesEQ p q = true → ProvableEQ p q) := by
  induction n using Nat.strong_induction_on with | h n ih =>
  have implies (p s q t) (h : polarLEQ p s q t = true) (lt : 2 * (p.size + q.size) < n) :=
    (ih _ lt).1 p s q t rfl h
  have equivalent {s} (p q : SimpleExpr s) (h : latticesEQ p q = true)
      (lt : 2 * (p.size + q.size) + 1 < n) := (ih _ lt).2 p q rfl h
  constructor
  · intro p s q t hn h
    unfold polarLEQ at h
    split at h
    · rename_i hi
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
      obtain ⟨rfl, he⟩ := hi
      exact ((ProvableEQ.of_toTerm he).withPolarity s).le
    · split at h
      case h_1 => exact (withPolarity_neg _ _).le.trans (implies _ _ _ _ h (by decrease hn))
      case h_2 => exact (implies _ _ _ _ h (by decrease hn)).trans (withPolarity_neg _ _).symm.le
      case h_3 => exact ProvableLE.bot _
      case h_4 => exact ProvableLE.top _
      -- Equalities may agree directly or after exchanging their operands.
      case h_5 =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ((ProvableEQ.equal (equivalent _ _ ha (by decrease hn)) (equivalent _ _ hb (by decrease hn))).withPolarity s).le
        · exact (((ProvableEQ.equal (equivalent _ _ ha (by decrease hn)) (equivalent _ _ hb (by decrease hn))).trans
            (ProvableEQ.equal_symm _ _)).withPolarity s).le
      -- Universal quantification preserves implication; negative polarity reverses it.
      case h_6 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        cases s
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (implies _ _ _ _ h (by decrease hn)).all.neg
        · simp only [↓reduceIte] at h
          exact (implies _ _ _ _ h (by decrease hn)).all
      -- To imply a conjunction, imply every factor.
      case h_7 =>
        apply ProvableLE.conj_right
        intro u hu
        have hsize := size_lt_conj hu
        simp only [SimpleExpr.size] at hsize
        exact implies _ _ _ _ (List.all_eq_true.mp h ⟨u, hu⟩ (List.mem_attach _ _)) (by decrease hn)
      -- Negation gives the dual rule for a conjunction on the left.
      case h_8 =>
        apply ProvableLE.neg_conj_left
        intro u hu
        have hsize := size_lt_conj hu
        simp only [SimpleExpr.size] at hsize
        exact implies _ _ _ _ (List.all_eq_true.mp h ⟨u, hu⟩ (List.mem_attach _ _)) (by decrease hn)
      -- A conjunction versus a negated conjunction can use a factor on either side.
      case h_9 =>
        simp only [Bool.or_eq_true, List.any_eq_true] at h
        rcases h with ⟨u, _, hu⟩ | ⟨u, _, hu⟩
        · have hsize := size_lt_conj u.property
          simp only [SimpleExpr.size] at hsize
          exact (ProvableLE.conj_member _ u.property).trans (implies _ _ _ _ hu (by decrease hn))
        · have hsize := size_lt_conj u.property
          simp only [SimpleExpr.size] at hsize
          exact (implies _ _ _ _ hu (by decrease hn)).trans (ProvableLE.conj_member _ u.property).neg
      -- One negated factor suffices to imply a negated conjunction.
      case h_10 =>
        obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
        have hsize := size_lt_conj u.property
        simp only [SimpleExpr.size] at hsize
        exact (implies _ _ _ _ hu (by decrease hn)).trans (ProvableLE.conj_member _ u.property).neg
      -- A conjunction can supply any one of its factors.
      case h_11 =>
        obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
        have hsize := size_lt_conj u.property
        simp only [SimpleExpr.size] at hsize
        exact (ProvableLE.conj_member _ u.property).trans (implies _ _ _ _ hu (by decrease hn))
      -- Applications require equivalence of both children, including at function sorts.
      case h_12 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        split at h
        · rename_i he; cases he
          simp only [Bool.and_eq_true] at h
          exact ((ProvableEQ.app (equivalent _ _ h.1 (by decrease hn)) (equivalent _ _ h.2 (by decrease hn))).withPolarity s).le
        · contradiction
      case h_13 => contradiction
  · intro s p q hn h
    unfold latticesEQ at h
    split at h
    · rename_i hi
      exact ProvableEQ.of_toTerm (of_decide_eq_true hi)
    · split at h
      case h_1 =>
        simp only [Bool.and_eq_true] at h
        exact ProvableEQ.of_le (implies _ _ _ _ h.1 (by decrease hn)) (implies _ _ _ _ h.2 (by decrease hn))
      case h_2 =>
        split at h
        · rename_i he; cases he
          simp only [Bool.and_eq_true] at h
          exact ProvableEQ.app (equivalent _ _ h.1 (by decrease hn)) (equivalent _ _ h.2 (by decrease hn))
        · contradiction
      case h_3 => exact ProvableEQ.lam _ (equivalent _ _ h (by decrease hn))
      case h_4 => contradiction

theorem polarLEQ_sound (p : SimpleExpr prop) (s : Bool) (q : SimpleExpr prop) (t : Bool)
    (h : polarLEQ p s q t = true) : ProvableLE (withPolarity p s) (withPolarity q t) :=
  (comparison_sound _).1 p s q t rfl h

theorem latticesEQ_sound {s : LSort} (p q : SimpleExpr s)
    (h : latticesEQ p q = true) : ProvableEQ p q := (comparison_sound _).2 p q rfl h
theorem latticesLEQ_sound {p q : SimpleExpr prop} (h : latticesLEQ p q = true) :
    ProvableLE p q := polarLEQ_sound p true q true h

end Lisa.Orthologic
