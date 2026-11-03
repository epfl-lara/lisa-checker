import Lisa.Checker.Interfaces
import Lisa.Order
import Lisa.Orthologic.Algebra

open Lisa Expr

namespace Lisa.Orthologic

/-- Optional concrete model used to establish direct expression laws. -/
structure Interpretation (leq : ExprRel) where
  Carrier : Type
  algebra : Ortholattice Carrier
  eval : Expr → Carrier
  compare : ∀ p q, leq p q ↔ eval p ≤ eval q
  top_eq : eval top = ⊤
  bot_eq : eval bot = ⊥
  and_eq : ∀ p q, eval (and p q) = eval p ⊓ eval q
  or_eq : ∀ p q, eval (or p q) = eval p ⊔ eval q
  neg_eq : ∀ p, eval (neg p) = (eval p)ᶜ
  imp_eq : ∀ p q, eval (imp p q) = (eval p)ᶜ ⊔ eval q
  iff_eq : ∀ p q, eval (iff p q) =
    ((eval p)ᶜ ⊔ eval q) ⊓ ((eval q)ᶜ ⊔ eval p)

namespace Interpretation
variable {leq : ExprRel}
instance (m : Interpretation leq) : Ortholattice m.Carrier := m.algebra

theorem same_iff (m : Interpretation leq) {p q : Expr} :
    isSame leq p q ↔ m.eval p = m.eval q := by
  simp only [isSame, m.compare]
  exact le_antisymm_iff.symm

@[reducible] def preorder (m : Interpretation leq) : IsPreorder Expr leq where
  refl p := (m.compare p p).mpr le_rfl
  trans p _ r hp hq := (m.compare p r).mpr (le_trans ((m.compare _ _).mp hp) ((m.compare _ _).mp hq))

variable (m : Interpretation leq)
include m

theorem le_top : ∀ p, leq p top := by
  intro p
  exact (m.compare p top).mpr (by rw [m.top_eq]; exact _root_.le_top)

theorem bot_le : ∀ p, leq bot p := by
  intro p
  exact (m.compare bot p).mpr (by rw [m.bot_eq]; exact _root_.bot_le)

theorem and_left : ∀ p q, leq (and p q) p := by
  intro p q
  exact (m.compare _ _).mpr (by rw [m.and_eq]; exact inf_le_left)

theorem and_right : ∀ p q, leq (and p q) q := by
  intro p q
  exact (m.compare _ _).mpr (by rw [m.and_eq]; exact inf_le_right)

theorem le_and : ∀ {p q r}, leq p q → leq p r → leq p (and q r) := by
  intro p q r hp hq
  exact (m.compare _ _).mpr (by rw [m.and_eq]; exact le_inf ((m.compare _ _).mp hp) ((m.compare _ _).mp hq))

theorem or_left : ∀ p q, leq p (or p q) := by
  intro p q
  exact (m.compare _ _).mpr (by rw [m.or_eq]; exact le_sup_left)

theorem or_right : ∀ p q, leq q (or p q) := by
  intro p q
  exact (m.compare _ _).mpr (by rw [m.or_eq]; exact le_sup_right)

theorem or_le : ∀ {p q r}, leq p r → leq q r → leq (or p q) r := by
  intro p q r hp hq
  exact (m.compare _ _).mpr (by rw [m.or_eq]; exact sup_le ((m.compare _ _).mp hp) ((m.compare _ _).mp hq))

theorem neg_le : ∀ {p q}, leq p q → leq (neg q) (neg p) := by
  intro p q hp
  exact (m.compare _ _).mpr (by rw [m.neg_eq, m.neg_eq]; exact Ortholattice.compl_antitone ((m.compare _ _).mp hp))

theorem double_neg : ∀ p, isSame leq (neg (neg p)) p := by
  intro p
  exact m.same_iff.mpr (by rw [m.neg_eq, m.neg_eq, Ortholattice.compl_involutive])

theorem excluded_middle : ∀ p, leq top (or p (neg p)) := by
  intro p
  exact (m.compare _ _).mpr (by rw [m.top_eq, m.or_eq, m.neg_eq, Ortholattice.sup_compl])

theorem imp_same : ∀ p q, isSame leq (imp p q) (or (neg p) q) := by
  intro p q
  exact m.same_iff.mpr (by rw [m.imp_eq, m.or_eq, m.neg_eq])

theorem iff_same : ∀ p q, isSame leq (iff p q) (and (imp p q) (imp q p)) := by
  intro p q
  exact m.same_iff.mpr (by rw [m.iff_eq, m.and_eq, m.imp_eq, m.imp_eq])

theorem self_le (p : Expr) : leq p p := (m.compare p p).mpr le_rfl
theorem transitive {p q r : Expr} (h : leq p q) (h' : leq q r) : leq p r :=
  (m.compare p r).mpr (le_trans ((m.compare p q).mp h) ((m.compare q r).mp h'))
theorem same_refl (p : Expr) : isSame leq p p := ⟨m.self_le p, m.self_le p⟩
theorem same_symm {p q} (h : isSame leq p q) : isSame leq q p :=
  m.same_iff.mpr (m.same_iff.mp h).symm
theorem same_trans {p q r} (h : isSame leq p q) (h' : isSame leq q r) :
    isSame leq p r := ⟨m.transitive h.1 h'.1, m.transitive h'.2 h.2⟩
theorem compare_congr {p p' q q'} (hp : isSame leq p p') (hq : isSame leq q q') :
    leq p q ↔ leq p' q' :=
  ⟨fun h => m.transitive hp.2 (m.transitive h hq.1), fun h => m.transitive hp.1 (m.transitive h hq.2)⟩
theorem and_mono {p p' q q'} (hp : leq p p') (hq : leq q q') :
    leq (and p q) (and p' q') := m.le_and (m.transitive (m.and_left _ _) hp) (m.transitive (m.and_right _ _) hq)
theorem or_mono {p p' q q'} (hp : leq p p') (hq : leq q q') :
    leq (or p q) (or p' q') := m.or_le (m.transitive hp (m.or_left _ _)) (m.transitive hq (m.or_right _ _))
theorem and_congr {p p' q q'} (hp : isSame leq p p') (hq : isSame leq q q') :
    isSame leq (and p q) (and p' q') := ⟨m.and_mono hp.1 hq.1, m.and_mono hp.2 hq.2⟩
theorem or_congr {p p' q q'} (hp : isSame leq p p') (hq : isSame leq q q') :
    isSame leq (or p q) (or p' q') := ⟨m.or_mono hp.1 hq.1, m.or_mono hp.2 hq.2⟩
theorem neg_congr {p q} (h : isSame leq p q) : isSame leq (neg p) (neg q) :=
  ⟨m.neg_le h.2, m.neg_le h.1⟩
theorem le_and_iff (p q r : Expr) : leq p (and q r) ↔ leq p q ∧ leq p r :=
  ⟨fun h => ⟨m.transitive h (m.and_left _ _), m.transitive h (m.and_right _ _)⟩, fun h => m.le_and h.1 h.2⟩
theorem or_le_iff (p q r : Expr) : leq (or p q) r ↔ leq p r ∧ leq q r :=
  ⟨fun h => ⟨m.transitive (m.or_left _ _) h, m.transitive (m.or_right _ _) h⟩, fun h => m.or_le h.1 h.2⟩

theorem neg_top : isSame leq (neg top) bot := by
  exact m.same_iff.mpr (by simp [m.neg_eq, m.top_eq, m.bot_eq])

theorem imp_mono {p p' q q'} (hp : leq p' p) (hq : leq q q') :
    leq (imp p q) (imp p' q') :=
  m.transitive (m.imp_same _ _).1 (m.transitive (m.or_mono (m.neg_le hp) hq) (m.imp_same _ _).2)

theorem imp_top (p : Expr) : isSame leq (imp top p) p :=
  m.same_trans (m.imp_same _ _) (m.same_trans (m.or_congr m.neg_top (m.same_refl p))
    ⟨m.or_le (m.bot_le _) (m.self_le _), m.or_right _ _⟩)

theorem imp_self (p : Expr) : isSame leq (imp p p) top :=
  ⟨m.le_top _, m.transitive (m.excluded_middle (neg p))
    (m.transitive (m.or_mono (m.self_le _) (m.double_neg p).1) (m.imp_same _ _).2)⟩

theorem and_compl (p : Expr) : isSame leq (and p (neg p)) bot :=
  m.same_iff.mpr (by simp [m.and_eq, m.neg_eq, m.bot_eq])

theorem le_fold_and (ps : List Expr) (p r : Expr) :
    leq r (ps.foldl and p) ↔ leq r p ∧ ∀ q ∈ ps, leq r q := by
  induction ps generalizing p with
  | nil => simp
  | cons q ps ih => simp [ih, m.le_and_iff, and_assoc]

theorem fold_or_le (ps : List Expr) (p r : Expr) :
    leq (ps.foldl or p) r ↔ leq p r ∧ ∀ q ∈ ps, leq q r := by
  induction ps generalizing p with
  | nil => simp
  | cons q ps ih => simp [ih, m.or_le_iff, and_assoc]

theorem le_foldFormulas_and (ps : List Expr) (r : Expr) :
    leq r (foldFormulas and top ps) ↔ ∀ q ∈ ps, leq r q := by
  cases ps <;> simp [foldFormulas, m.le_fold_and, m.le_top]

theorem foldFormulas_or_le (ps : List Expr) (r : Expr) :
    leq (foldFormulas or bot ps) r ↔ ∀ q ∈ ps, leq q r := by
  cases ps <;> simp [foldFormulas, m.fold_or_le, m.bot_le]

theorem le_conjunction (Γ : Finset Expr) (r : Expr) :
    leq r (conjunction Γ) ↔ ∀ q ∈ Γ, leq r q := by
  simp [conjunction, m.le_foldFormulas_and]

theorem disjunction_le (Δ : Finset Expr) (r : Expr) :
    leq (disjunction Δ) r ↔ ∀ q ∈ Δ, leq q r := by
  simp [disjunction, m.foldFormulas_or_le]

theorem fold_and_same (ps : List Expr) :
    isSame leq (foldFormulas and top ps) (conjunction ps.toFinset) := by
  constructor
  · rw [m.le_conjunction (leq := leq)]
    simpa using (m.le_foldFormulas_and ps _).mp (m.self_le (leq := leq) _)
  · rw [m.le_foldFormulas_and (leq := leq)]
    simpa using (m.le_conjunction ps.toFinset _).mp (m.self_le (leq := leq) _)

theorem fold_or_same (ps : List Expr) :
    isSame leq (foldFormulas or bot ps) (disjunction ps.toFinset) := by
  constructor
  · rw [m.foldFormulas_or_le (leq := leq)]
    simpa using (m.disjunction_le ps.toFinset _).mp (m.self_le (leq := leq) _)
  · rw [m.disjunction_le (leq := leq)]
    simpa using (m.foldFormulas_or_le ps _).mp (m.self_le (leq := leq) _)

theorem imp_congr {p p' q q'} (hp : isSame leq p p') (hq : isSame leq q q') :
    isSame leq (imp p q) (imp p' q') := ⟨m.imp_mono hp.2 hq.1, m.imp_mono hp.1 hq.2⟩

theorem sequent_same_imp (Γ Δ : Finset Expr) :
    isSame leq (sequentToFormula Γ Δ) (imp (conjunction Γ) (disjunction Δ)) := by
  unfold sequentToFormula
  split
  · rename_i h
    subst Γ
    simpa [conjunction, foldFormulas] using m.same_symm (m.imp_top (leq := leq) (disjunction Δ))
  · exact m.same_refl _

theorem listSequent_same (pre post : List Expr) :
    isSame leq (listSequentToFormula pre post)
      (sequentToFormula pre.toFinset post.toFinset) := by
  cases pre with
  | nil => simpa [listSequentToFormula, sequentToFormula] using m.fold_or_same (leq := leq) post
  | cons p ps =>
    simp only [listSequentToFormula, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact m.same_trans (m.imp_congr (m.fold_and_same _) (m.fold_or_same _))
      (m.same_symm (m.sequent_same_imp _ _))

theorem sequentLeq_of_setLeq {Γ Δ Γ' Δ' : Finset Expr}
    (hΓ : setLeq leq Γ Γ') (hΔ : setLeq leq Δ Δ') :
    sequentLeq leq Γ Δ Γ' Δ' := by
  apply m.transitive (m.sequent_same_imp Γ Δ).1
  apply m.transitive _ (m.sequent_same_imp Γ' Δ').2
  apply m.imp_mono
  · apply (m.le_conjunction _ _).mpr
    intro p hp
    obtain ⟨q, hq, heq⟩ := hΓ p hp
    exact m.transitive ((m.le_conjunction Γ' _).mp (m.self_le _) q hq) heq.2
  · apply (m.disjunction_le _ _).mpr
    intro p hp
    obtain ⟨q, hq, heq⟩ := hΔ p hp
    exact m.transitive heq.1 ((m.disjunction_le Δ' _).mp (m.self_le _) q hq)

section Reduction

variable [OrderReduction leq]

theorem map_reduce_and (p q : Expr) :
    isSame leq (OrderReduction.reduce (leq := leq) (and p q))
      (and (OrderReduction.reduce (leq := leq) p) (OrderReduction.reduce (leq := leq) q)) :=
  m.same_trans (OrderReduction.preserves _) (m.same_symm
    (m.and_congr (OrderReduction.preserves p) (OrderReduction.preserves q)))

theorem map_reduce_or (p q : Expr) :
    isSame leq (OrderReduction.reduce (leq := leq) (or p q))
      (or (OrderReduction.reduce (leq := leq) p) (OrderReduction.reduce (leq := leq) q)) :=
  m.same_trans (OrderReduction.preserves _) (m.same_symm
    (m.or_congr (OrderReduction.preserves p) (OrderReduction.preserves q)))

theorem map_reduce_neg (p : Expr) :
    isSame leq (OrderReduction.reduce (leq := leq) (neg p)) (neg (OrderReduction.reduce (leq := leq) p)) :=
  m.same_trans (OrderReduction.preserves _) (m.same_symm
    (m.neg_congr (OrderReduction.preserves p)))

end Reduction

@[reducible] def sequentEncoding : SequentEncoding leq where
  compare pre post p := ⟨m.compare_congr (m.listSequent_same pre post) (m.same_refl p),
    m.compare_congr (m.same_refl p) (m.listSequent_same pre post)⟩

theorem listSequent (pre post : List Expr) :
    m.eval (listSequentToFormula pre post) =
      m.eval (sequentToFormula pre.toFinset post.toFinset) :=
  m.same_iff.mp (m.listSequent_same pre post)

end Interpretation
end Lisa.Orthologic
