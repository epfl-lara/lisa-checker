import Lisa.Syntax
import Lisa.Orthologic.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Basic

open Lisa Expr

abbrev Order := Expr → Expr → Prop

/-- Compare expressions in both directions of an order. -/
def isSame (leq : Order) (p q : Expr) : Prop := leq p q ∧ leq q p

/-- Interpret the expression order in an ortholattice.

Antisymmetry holds in the algebra, rather than on expression syntax. This lets
distinct expressions represent the same element without identifying Lean terms.
-/
class OrderAlgebra (leq : Order) where
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

@[reducible] instance {leq : Order} [OrderAlgebra leq] :
    Ortholattice (OrderAlgebra.Carrier (leq := leq)) := OrderAlgebra.algebra

/-- Preserve sorts and both order comparisons when reducing expressions.

Transitivity suffices to derive monotonicity and sound reduced matching.
Do not require a particular normalization algorithm or syntactic idempotence.
-/
class OrderReduction (leq : Order) where
  reduce : Expr → Expr
  preserves : ∀ p, isSame leq (reduce p) p
  preservesSort : ∀ p, (reduce p).sort = p.sort

/-- Preserve equality formulas when their individual terms are order-equivalent. -/
class TermEqualityCongruence (leq : Order) where
  congr : ∀ {s s' t t'}, isTerm s → isTerm s' → isTerm t → isTerm t' →
    isSame leq s s' → isSame leq t t' → isSame leq (eq s t) (eq s' t')

def reducedSame (leq : Order) [OrderReduction leq] (p q : Expr) : Prop :=
  OrderReduction.reduce (leq := leq) p = OrderReduction.reduce (leq := leq) q

def ordContains (leq : Order) (p : Expr) (Γ : Finset Expr) : Prop :=
  ∃ q ∈ Γ, isSame leq p q

def setLeq (leq : Order) (Γ Δ : Finset Expr) : Prop :=
  ∀ p ∈ Γ, ∃ q ∈ Δ, isSame leq p q

/-- Match every retained formula by equality of reduced expressions. -/
def reducedSubset (leq : Order) [OrderReduction leq] (Γ Δ : Finset Expr) : Prop :=
  ∀ p ∈ Γ, ∃ q ∈ Δ, reducedSame leq p q

/-- Permit one removed principal formula up to full order equality. -/
def containedExcept (leq : Order) [OrderReduction leq]
    (Γ Δ : Finset Expr) (p : Expr) : Prop :=
  ∀ q ∈ Γ, (∃ r ∈ Δ, reducedSame leq q r) ∨ isSame leq q p

/-- Retain literal context members, or match either principal formula by the order. -/
def containedExceptEither (leq : Order) (Γ Δ : Finset Expr) (p q : Expr) : Prop :=
  ∀ r ∈ Γ, r ∈ Δ ∨ isSame leq r p ∨ isSame leq r q

/-- Fold a nonempty list from its first expression, as in Lisa's kernel. -/
def foldFormulas (op : Expr → Expr → Expr) (unit : Expr) : List Expr → Expr
  | [] => unit
  | p :: ps => ps.foldl op p

/-- Encode a wire sequent without choosing an enumeration of a finite set. -/
def listSequentToFormula (pre post : List Expr) : Expr :=
  if pre.isEmpty then foldFormulas or bot post
  else imp (foldFormulas and top pre) (foldFormulas or bot post)

noncomputable def conjunction (Γ : Finset Expr) : Expr :=
  foldFormulas and top Γ.toList

noncomputable def disjunction (Δ : Finset Expr) : Expr :=
  foldFormulas or bot Δ.toList

/-- Encode a sequent by the kernel's conjunction, implication, and disjunction. -/
noncomputable def sequentToFormula (Γ Δ : Finset Expr) : Expr :=
  if Γ = ∅ then disjunction Δ else imp (conjunction Γ) (disjunction Δ)

noncomputable def sequentLeq (leq : Order) (Γ Δ Γ' Δ' : Finset Expr) : Prop :=
  leq (sequentToFormula Γ Δ) (sequentToFormula Γ' Δ')

/-- Preserve comparisons when replacing wire lists by their finite-set encoding.

This is a representation law, not an assumption of logical soundness. It covers
permutation and duplicate removal on both sides of a whole sequent.
-/
class SequentEncoding (leq : Order) : Prop where
  compare : ∀ (pre post : List Expr) (p : Expr),
    (leq (listSequentToFormula pre post) p ↔
      leq (sequentToFormula pre.toFinset post.toFinset) p) ∧
    (leq p (listSequentToFormula pre post) ↔
      leq p (sequentToFormula pre.toFinset post.toFinset))

/-- Lift equivalent member inclusion to whole-sequent weakening. -/
class SequentWeakening (leq : Order) : Prop where
  weaken : ∀ {Γ Δ Γ' Δ' : Finset Expr},
    setLeq leq Γ Γ' → setLeq leq Δ Δ' → sequentLeq leq Γ Δ Γ' Δ'

/-- Bound every whole-sequent interpretation above by the truth expression. -/
class SequentTruth (leq : Order) : Prop where
  greatest : ∀ Γ Δ : Finset Expr, leq (sequentToFormula Γ Δ) top

/-- Supply exactly the interfaces needed by executable linear checking.

No preorder or logical interpretation is required here. Accepted certificates
are sound relative to this order; transfer to a reference calculus is separate.
-/
class CheckerOrder (leq : Order) extends SequentEncoding leq, OrderReduction leq where
  decision : DecidableRel leq

instance {leq : Order} [CheckerOrder leq] : DecidableRel leq :=
  CheckerOrder.decision

/-- Bundle existing checker interfaces without introducing new order laws. -/
@[reducible] def CheckerOrder.of (leq : Order) [SequentEncoding leq] [OrderReduction leq]
    [DecidableRel leq] : CheckerOrder leq where
  toSequentEncoding := inferInstance
  toOrderReduction := inferInstance
  decision := inferInstance

/-- Supply the laws needed to attach an arbitrary fixed set of imports. -/
class ImportOrder (leq : Order) extends OrderReduction leq, Std.Refl leq, SequentTruth leq

/-- Bundle the minimal fixed-import assumptions. -/
@[reducible] def ImportOrder.of (leq : Order) [OrderReduction leq] [Std.Refl leq]
    [SequentTruth leq] :
    ImportOrder leq where
  toOrderReduction := inferInstance
  toRefl := inferInstance
  toSequentTruth := inferInstance

/-- Supply the structural laws for equivalence of Ordered and Weakened proofs.

This strengthens ImportOrder, not CheckerOrder. In particular, a union of
executable comparison backends need not satisfy the transitivity required here.
-/
class ProofOrder (leq : Order) extends ImportOrder leq, IsPreorder Expr leq,
    SequentWeakening leq, TermEqualityCongruence leq

/-- Bundle the structural translation assumptions without an algebraic carrier. -/
@[reducible] def ProofOrder.of (leq : Order) [OrderReduction leq] [IsPreorder Expr leq]
    [SequentWeakening leq] [SequentTruth leq] [TermEqualityCongruence leq] :
    ProofOrder leq where
  toImportOrder := ImportOrder.of leq
  trans := fun p q r => IsTrans.trans p q r
  toSequentWeakening := inferInstance
  toTermEqualityCongruence := inferInstance

namespace OrderLaws

@[simp] theorem self_le {leq : Order} [Std.Refl leq] (p : Expr) : leq p p :=
  Std.Refl.refl p

theorem transitive {leq : Order} [IsTrans Expr leq] {p q r : Expr}
    (h₁ : leq p q) (h₂ : leq q r) : leq p r :=
  IsTrans.trans p q r h₁ h₂

end OrderLaws

/-- Obtain the reverse truth comparison by ordinary whole-sequent weakening. -/
theorem SequentWeakening.top_hypothesis {leq : Order}
    [Std.Refl leq] [SequentWeakening leq] :
    leq top (sequentToFormula {top} {top}) := by
  have h : sequentLeq leq ∅ {top} {top} {top} :=
    SequentWeakening.weaken
      (fun p hp => False.elim (Finset.notMem_empty p hp))
      (fun p hp => ⟨p, hp, OrderLaws.self_le p, OrderLaws.self_le p⟩)
  simpa [sequentLeq, sequentToFormula, disjunction, foldFormulas] using h

namespace OrderAlgebra

variable {leq : Order} [OrderAlgebra leq]

@[simp] theorem reflexive : Reflexive leq := fun p => (compare p p).mpr le_rfl

@[simp] theorem self_le (p : Expr) : leq p p := reflexive p

theorem transitive {p q r : Expr} (h₁ : leq p q) (h₂ : leq q r) : leq p r :=
  (compare _ _).mpr (le_trans ((compare _ _).mp h₁) ((compare _ _).mp h₂))

instance : IsPreorder Expr leq where
  refl := reflexive
  trans := fun _ _ _ => transitive

theorem same_iff {p q : Expr} :
    isSame leq p q ↔ eval (leq := leq) p = eval (leq := leq) q := by
  simp only [isSame, compare (leq := leq)]
  exact le_antisymm_iff.symm

@[simp] theorem value_fold_and (ps : List Expr) (p : Expr) :
    eval (leq := leq) (ps.foldl and p) =
      eval (leq := leq) p ⊓ ps.toFinset.inf (eval (leq := leq)) := by
  induction ps generalizing p with
  | nil => simp
  | cons q ps ih =>
      simp only [List.foldl_cons, ih, and_eq, List.toFinset_cons,
        Finset.inf_insert, inf_assoc]

@[simp] theorem value_fold_or (ps : List Expr) (p : Expr) :
    eval (leq := leq) (ps.foldl or p) =
      eval (leq := leq) p ⊔ ps.toFinset.sup (eval (leq := leq)) := by
  induction ps generalizing p with
  | nil => simp
  | cons q ps ih =>
      simp only [List.foldl_cons, ih, or_eq, List.toFinset_cons,
        Finset.sup_insert, sup_assoc]

@[simp] theorem value_conjunction (Γ : Finset Expr) :
    eval (leq := leq) (conjunction Γ) = Γ.inf (eval (leq := leq)) := by
  have h : ∀ ps : List Expr, eval (leq := leq) (foldFormulas and top ps) =
      ps.toFinset.inf (eval (leq := leq)) := by
    intro ps
    cases ps <;> simp [foldFormulas, top_eq, ← value_fold_and]
  simpa [conjunction] using h Γ.toList

@[simp] theorem value_disjunction (Δ : Finset Expr) :
    eval (leq := leq) (disjunction Δ) = Δ.sup (eval (leq := leq)) := by
  have h : ∀ ps : List Expr, eval (leq := leq) (foldFormulas or bot ps) =
      ps.toFinset.sup (eval (leq := leq)) := by
    intro ps
    cases ps <;> simp [foldFormulas, bot_eq, ← value_fold_or]
  simpa [disjunction] using h Δ.toList

theorem compl_top : (⊤ : Carrier (leq := leq))ᶜ = ⊥ := by
  have h : (⊥ : Carrier (leq := leq))ᶜ = ⊤ := by
    simpa using Ortholattice.sup_compl (⊥ : Carrier (leq := leq))
  rw [← h, Ortholattice.compl_involutive]

@[simp] theorem value_sequent (Γ Δ : Finset Expr) :
    eval (leq := leq) (sequentToFormula Γ Δ) =
      (Γ.inf (eval (leq := leq)))ᶜ ⊔ Δ.sup (eval (leq := leq)) := by
  unfold sequentToFormula
  split
  · subst Γ
    simp [compl_top]
  · simp only [imp_eq]
    rw [value_conjunction, value_disjunction]

theorem sequentLeq_of_setLeq {Γ Δ Γ' Δ' : Finset Expr}
    (hΓ : setLeq leq Γ Γ') (hΔ : setLeq leq Δ Δ') :
    sequentLeq leq Γ Δ Γ' Δ' := by
  rw [sequentLeq, compare (leq := leq), value_sequent, value_sequent]
  apply sup_le_sup
  · apply Ortholattice.compl_antitone
    apply Finset.le_inf
    intro p hp
    obtain ⟨q, hq, heq⟩ := hΓ p hp
    rw [same_iff.mp heq]
    exact Finset.inf_le hq
  · apply Finset.sup_le
    intro p hp
    obtain ⟨q, hq, heq⟩ := hΔ p hp
    rw [same_iff.mp heq]
    exact Finset.le_sup hq

/-- Identify a wire fold with the finite-set interpretation in an algebra. -/
theorem value_listSequent (pre post : List Expr) :
    eval (leq := leq) (listSequentToFormula pre post) =
      eval (leq := leq) (sequentToFormula pre.toFinset post.toFinset) := by
  have hand : ∀ ps : List Expr, eval (leq := leq) (foldFormulas and top ps) =
      ps.toFinset.inf (eval (leq := leq)) := by
    intro ps
    cases ps <;> simp [foldFormulas, top_eq, ← value_fold_and]
  have hor : ∀ ps : List Expr, eval (leq := leq) (foldFormulas or bot ps) =
      ps.toFinset.sup (eval (leq := leq)) := by
    intro ps
    cases ps <;> simp [foldFormulas, bot_eq, ← value_fold_or]
  rw [value_sequent]
  cases pre <;>
    simp [listSequentToFormula, imp_eq, hand, hor, compl_top]

instance : SequentEncoding leq where
  compare := by
    intro pre post p
    simp only [compare, value_listSequent, and_self]

instance : SequentWeakening leq where
  weaken := sequentLeq_of_setLeq

instance : SequentTruth leq where
  greatest := by
    intro Γ Δ
    rw [compare (leq := leq), top_eq]
    exact le_top

end OrderAlgebra

namespace OrderReduction

variable {leq : Order} [OrderReduction leq]

theorem leq_iff [IsTrans Expr leq] (p q : Expr) :
    leq (reduce (leq := leq) p) (reduce (leq := leq) q) ↔ leq p q := by
  obtain ⟨hp, hp'⟩ := preserves (leq := leq) p
  obtain ⟨hq, hq'⟩ := preserves (leq := leq) q
  constructor
  · intro h
    exact OrderLaws.transitive hp' (OrderLaws.transitive h hq)
  · intro h
    exact OrderLaws.transitive hp (OrderLaws.transitive h hq')

theorem monotone [IsTrans Expr leq] {p q : Expr} (h : leq p q) :
    leq (reduce (leq := leq) p) (reduce (leq := leq) q) :=
  (leq_iff p q).mpr h

/-- Recover original order-equivalence from equality of reduced expressions. -/
theorem sound [IsTrans Expr leq] (p q : Expr)
    (h : reduce (leq := leq) p = reduce (leq := leq) q) : isSame leq p q := by
  obtain ⟨hp, hp'⟩ := preserves (leq := leq) p
  obtain ⟨hq, hq'⟩ := preserves (leq := leq) q
  rw [h] at hp hp'
  exact ⟨OrderLaws.transitive hp' hq, OrderLaws.transitive hq' hp⟩

theorem map_top : isSame leq (reduce (leq := leq) top) top := preserves top

theorem map_bot : isSame leq (reduce (leq := leq) bot) bot := preserves bot

variable [OrderAlgebra leq]

@[simp] theorem value_reduce (p : Expr) :
    OrderAlgebra.eval (reduce (leq := leq) p) = OrderAlgebra.eval (leq := leq) p :=
  OrderAlgebra.same_iff.mp (preserves p)

theorem map_and (p q : Expr) :
    isSame leq (reduce (leq := leq) (and p q))
      (and (reduce (leq := leq) p) (reduce (leq := leq) q)) := by
  apply OrderAlgebra.same_iff.mpr
  simp only [value_reduce, OrderAlgebra.and_eq]

theorem map_or (p q : Expr) :
    isSame leq (reduce (leq := leq) (or p q))
      (or (reduce (leq := leq) p) (reduce (leq := leq) q)) := by
  apply OrderAlgebra.same_iff.mpr
  simp only [value_reduce, OrderAlgebra.or_eq]

theorem map_neg (p : Expr) :
    isSame leq (reduce (leq := leq) (neg p)) (neg (reduce (leq := leq) p)) := by
  apply OrderAlgebra.same_iff.mpr
  simp only [value_reduce, OrderAlgebra.neg_eq]

end OrderReduction

theorem TermEqualityCongruence.refl_eq {leq : Order} [Std.Refl leq]
    [TermEqualityCongruence leq] {s t : Expr} (hs : isTerm s) (ht : isTerm t)
    (h : isSame leq s t) : isSame leq (eq s s) (eq s t) :=
  TermEqualityCongruence.congr hs hs hs ht
    ⟨OrderLaws.self_le s, OrderLaws.self_le s⟩ h

@[simp] theorem reducedSame_refl {leq : Order} [OrderReduction leq] (p : Expr) :
    reducedSame leq p p := rfl

theorem reducedSubset_of_subset {leq : Order} [OrderReduction leq]
    {Γ Δ : Finset Expr} (h : Γ ⊆ Δ) : reducedSubset leq Γ Δ :=
  fun p hp => ⟨p, h hp, rfl⟩

theorem setLeq_of_reducedSubset {leq : Order} [IsTrans Expr leq] [OrderReduction leq]
    {Γ Δ : Finset Expr} (h : reducedSubset leq Γ Δ) : setLeq leq Γ Δ := by
  intro p hp
  obtain ⟨q, hq, heq⟩ := h p hp
  exact ⟨q, hq, OrderReduction.sound p q heq⟩

theorem containedExcept_of_sdiff {leq : Order} [OrderReduction leq]
    {Γ Δ : Finset Expr} {p : Expr}
    (h : ∀ q ∈ Γ \ Δ, isSame leq p q) : containedExcept leq Γ Δ p := by
  intro q hq
  by_cases hΔ : q ∈ Δ
  · exact Or.inl ⟨q, hΔ, rfl⟩
  · have heq := h q (Finset.mem_sdiff.mpr ⟨hq, hΔ⟩)
    exact Or.inr ⟨heq.2, heq.1⟩

theorem containedExceptEither_of_sdiff {leq : Order}
    {Γ Δ : Finset Expr} {p q : Expr}
    (h : ∀ r ∈ Γ \ Δ, isSame leq p r ∨ isSame leq q r) :
    containedExceptEither leq Γ Δ p q := by
  intro r hr
  by_cases hΔ : r ∈ Δ
  · exact Or.inl hΔ
  · rcases h r (Finset.mem_sdiff.mpr ⟨hr, hΔ⟩) with hp | hq
    · exact Or.inr (Or.inl ⟨hp.2, hp.1⟩)
    · exact Or.inr (Or.inr ⟨hq.2, hq.1⟩)
