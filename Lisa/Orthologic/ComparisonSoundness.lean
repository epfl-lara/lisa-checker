import Lisa.Orthologic.Provability
import Lisa.Orthologic.Comparison

/-! Soundness of the mutually recursive comparisons in `Ordered AlphaBetaEta`.
The joint induction uses the same measure as the executable definitions.
-/

namespace Lisa.Orthologic
open SimpleExpr

theorem ProvableEQ.polar {p q : SimpleExpr prop} (h : ProvableEQ p q) (s : Bool) :
    ProvableEQ (polar p s) (polar q s) := by cases s <;> first | exact h | exact h.neg

theorem polar_neg (p : SimpleExpr prop) (s : Bool) :
    ProvableEQ (polar (.neg p) s) (polar p (!s)) := by
  cases s
  · exact ProvableEQ.of_le (ProvableLE.doubleNegElim p) (ProvableLE.doubleNegIntro p)
  · exact ProvableEQ.refl _

local macro "decrease" hn:ident : tactic => `(tactic|
  (try simp only [SimpleExpr.size] at $hn ⊢
   omega))

private theorem comparison_sound (n : Nat) :
    (∀ p s q t, 2 * (p.size + q.size) = n → polarLEQ p s q t = true →
      ProvableLE (polar p s) (polar q t)) ∧
    (∀ {s : LSort} (p q : SimpleExpr s), 2 * (p.size + q.size) + 1 = n →
      latticesEQ p q = true → ProvableEQ p q) := by
  induction n using Nat.strong_induction_on with | h n ih =>
  have pl (p s q t) (h : polarLEQ p s q t = true) (lt : 2 * (p.size + q.size) < n) :=
    (ih _ lt).1 p s q t rfl h
  have eqv {s} (p q : SimpleExpr s) (h : latticesEQ p q = true)
      (lt : 2 * (p.size + q.size) + 1 < n) := (ih _ lt).2 p q rfl h
  constructor
  · intro p s q t hn h
    unfold polarLEQ at h
    split at h
    · rename_i hi
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
      obtain ⟨rfl, he⟩ := hi
      exact ((ProvableEQ.of_toTerm he).polar s).le
    · split at h
      case h_1 => exact (polar_neg _ _).le.trans (pl _ _ _ _ h (by decrease hn))
      case h_2 => exact (pl _ _ _ _ h (by decrease hn)).trans (polar_neg _ _).symm.le
      case h_3 => exact ProvableLE.bot _
      case h_4 => exact ProvableLE.top _
      case h_5 =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ((ProvableEQ.equal (eqv _ _ ha (by decrease hn)) (eqv _ _ hb (by decrease hn))).polar s).le
        · exact (((ProvableEQ.equal (eqv _ _ ha (by decrease hn)) (eqv _ _ hb (by decrease hn))).trans
            (ProvableEQ.equal_symm _ _)).polar s).le
      case h_6 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        cases s
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (pl _ _ _ _ h (by decrease hn)).all.neg
        · simp only [↓reduceIte] at h
          exact (pl _ _ _ _ h (by decrease hn)).all
      case h_7 =>
        apply ProvableLE.conj_right
        intro u hu
        have hsize := size_lt_conj hu
        simp only [SimpleExpr.size] at hsize
        exact pl _ _ _ _ (List.all_eq_true.mp h ⟨u, hu⟩ (List.mem_attach _ _)) (by decrease hn)
      case h_8 =>
        apply ProvableLE.neg_conj_left
        intro u hu
        have hsize := size_lt_conj hu
        simp only [SimpleExpr.size] at hsize
        exact pl _ _ _ _ (List.all_eq_true.mp h ⟨u, hu⟩ (List.mem_attach _ _)) (by decrease hn)
      case h_9 =>
        simp only [Bool.or_eq_true, List.any_eq_true] at h
        rcases h with ⟨u, _, hu⟩ | ⟨u, _, hu⟩
        · have hsize := size_lt_conj u.property
          simp only [SimpleExpr.size] at hsize
          exact (ProvableLE.conj_member _ u.property).trans (pl _ _ _ _ hu (by decrease hn))
        · have hsize := size_lt_conj u.property
          simp only [SimpleExpr.size] at hsize
          exact (pl _ _ _ _ hu (by decrease hn)).trans (ProvableLE.conj_member _ u.property).neg
      case h_10 =>
        obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
        have hsize := size_lt_conj u.property
        simp only [SimpleExpr.size] at hsize
        exact (pl _ _ _ _ hu (by decrease hn)).trans (ProvableLE.conj_member _ u.property).neg
      case h_11 =>
        obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
        have hsize := size_lt_conj u.property
        simp only [SimpleExpr.size] at hsize
        exact (ProvableLE.conj_member _ u.property).trans (pl _ _ _ _ hu (by decrease hn))
      case h_12 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        split at h
        · rename_i he; cases he
          simp only [Bool.and_eq_true] at h
          exact ((ProvableEQ.app (eqv _ _ h.1 (by decrease hn)) (eqv _ _ h.2 (by decrease hn))).polar s).le
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
        exact ProvableEQ.of_le (pl _ _ _ _ h.1 (by decrease hn)) (pl _ _ _ _ h.2 (by decrease hn))
      case h_2 =>
        split at h
        · rename_i he; cases he
          simp only [Bool.and_eq_true] at h
          exact ProvableEQ.app (eqv _ _ h.1 (by decrease hn)) (eqv _ _ h.2 (by decrease hn))
        · contradiction
      case h_3 => exact ProvableEQ.lam _ (eqv _ _ h (by decrease hn))
      case h_4 => contradiction
  
theorem polarLEQ_sound (p : SimpleExpr prop) (s : Bool) (q : SimpleExpr prop) (t : Bool)
    (h : polarLEQ p s q t = true) : ProvableLE (polar p s) (polar q t) :=
  (comparison_sound _).1 p s q t rfl h

theorem latticesEQ_sound {s : LSort} (p q : SimpleExpr s)
    (h : latticesEQ p q = true) : ProvableEQ p q := (comparison_sound _).2 p q rfl h
theorem latticesLEQ_sound {p q : SimpleExpr prop} (h : latticesLEQ p q = true) :
    ProvableLE p q := polarLEQ_sound p true q true h

end Lisa.Orthologic
