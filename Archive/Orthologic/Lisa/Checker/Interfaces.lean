import Lisa.Order

open Lisa Expr

/-- Preserve sorts and both order comparisons when reducing expressions.

`reflect` certifies the equality shortcut even for nontransitive backends.
Do not require a particular normalization algorithm or syntactic idempotence.
-/
class OrderReduction (leq : ExprRel) where
  reduce : Expr → Expr
  preserves : ∀ p, isSame leq (reduce p) p
  reflect : ∀ p q, reduce p = reduce q → isSame leq p q
  preservesSort : ∀ p, (reduce p).sort = p.sort

def reducedSame (leq : ExprRel) [OrderReduction leq] (p q : Expr) : Prop :=
  OrderReduction.reduce (leq := leq) p = OrderReduction.reduce (leq := leq) q

/-- Match every retained formula by equality of reduced expressions. -/
def reducedSubset (leq : ExprRel) [OrderReduction leq] (Γ Δ : Finset Expr) : Prop :=
  ∀ p ∈ Γ, ∃ q ∈ Δ, reducedSame leq p q

/-- Encode a wire sequent without choosing an enumeration of a finite set. -/
def listSequentToFormula (pre post : List Expr) : Expr :=
  if pre.isEmpty then foldFormulas or bot post
  else imp (foldFormulas and top pre) (foldFormulas or bot post)

/-- Preserve comparisons when replacing wire lists by their finite-set encoding.

This is a representation law, not an assumption of logical soundness. It covers
permutation and duplicate removal on both sides of a whole sequent.
-/
class SequentEncoding (leq : ExprRel) : Prop where
  compare : ∀ (pre post : List Expr) (p : Expr),
    (leq (listSequentToFormula pre post) p ↔
      leq (sequentToFormula pre.toFinset post.toFinset) p) ∧
    (leq p (listSequentToFormula pre post) ↔
      leq p (sequentToFormula pre.toFinset post.toFinset))

/-- Supply exactly the interfaces needed by executable linear checking.

No preorder or logical interpretation is required here. Accepted certificates
are sound relative to this order; transfer to a reference calculus is separate.
-/
class CheckerOrder (leq : ExprRel) extends SequentEncoding leq, OrderReduction leq where
  decision : DecidableRel leq

instance {leq : ExprRel} [CheckerOrder leq] : DecidableRel leq :=
  CheckerOrder.decision

/-- Bundle existing checker interfaces without introducing new order laws. -/
@[reducible] def CheckerOrder.of (leq : ExprRel) [SequentEncoding leq] [OrderReduction leq]
    [DecidableRel leq] : CheckerOrder leq where
  toSequentEncoding := inferInstance
  toOrderReduction := inferInstance
  decision := inferInstance

namespace OrderReduction

variable {leq : ExprRel} [OrderReduction leq]

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
theorem sound (p q : Expr)
    (h : reduce (leq := leq) p = reduce (leq := leq) q) : isSame leq p q :=
  reflect p q h

theorem map_top : isSame leq (reduce (leq := leq) top) top := preserves top

theorem map_bot : isSame leq (reduce (leq := leq) bot) bot := preserves bot

end OrderReduction

@[simp] theorem reducedSame_refl {leq : ExprRel} [OrderReduction leq] (p : Expr) :
    reducedSame leq p p := rfl

theorem reducedSubset_of_subset {leq : ExprRel} [OrderReduction leq]
    {Γ Δ : Finset Expr} (h : Γ ⊆ Δ) : reducedSubset leq Γ Δ :=
  fun p hp => ⟨p, h hp, rfl⟩

theorem setLeq_of_reducedSubset {leq : ExprRel} [OrderReduction leq]
    {Γ Δ : Finset Expr} (h : reducedSubset leq Γ Δ) : setLeq leq Γ Δ := by
  intro p hp
  obtain ⟨q, hq, heq⟩ := h p hp
  exact ⟨q, hq, OrderReduction.sound p q heq⟩

namespace OrderReduction

/-- Build a certified reducer from preservation when the comparison is transitive. -/
@[reducible] def of {leq : ExprRel} [IsTrans Expr leq]
    (reduce : Expr → Expr) (preserves : ∀ p, isSame leq (reduce p) p)
    (preservesSort : ∀ p, (reduce p).sort = p.sort) : OrderReduction leq where
  reduce := reduce
  preserves := preserves
  preservesSort := preservesSort
  reflect p q h := by
    obtain ⟨hp, hp'⟩ := preserves p
    obtain ⟨hq, hq'⟩ := preserves q
    rw [h] at hp hp'
    exact ⟨OrderLaws.transitive hp' hq, OrderLaws.transitive hq' hp⟩

end OrderReduction
