import Lisa.Syntax
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Basic

open Lisa Expr

/-- An expression relation; laws are supplied separately. -/
abbrev ExprRel := Expr → Expr → Prop

def isSame (leq : ExprRel) (p q : Expr) : Prop := leq p q ∧ leq q p

def ordContains (leq : ExprRel) (p : Expr) (Γ : Finset Expr) : Prop :=
  ∃ q ∈ Γ, isSame leq p q

def setLeq (leq : ExprRel) (Γ Δ : Finset Expr) : Prop :=
  ∀ p ∈ Γ, ∃ q ∈ Δ, isSame leq p q

/-- Permit one removed principal formula up to full order equality. -/
def containedExcept (leq : ExprRel)
    (Γ Δ : Finset Expr) (p : Expr) : Prop :=
  ∀ q ∈ Γ, (∃ r ∈ Δ, isSame leq q r) ∨ isSame leq q p

/-- Match retained context members or either principal formula by equivalence. -/
def containedExceptEither (leq : ExprRel) (Γ Δ : Finset Expr) (p q : Expr) : Prop :=
  ∀ r ∈ Γ, (∃ s ∈ Δ, isSame leq r s) ∨ isSame leq r p ∨ isSame leq r q

/-- Fold a nonempty list from its first expression, as in Lisa's kernel. -/
def foldFormulas (op : Expr → Expr → Expr) (unit : Expr) : List Expr → Expr
  | [] => unit
  | p :: ps => ps.foldl op p

noncomputable def conjunction (Γ : Finset Expr) : Expr :=
  foldFormulas and top Γ.toList

noncomputable def disjunction (Δ : Finset Expr) : Expr :=
  foldFormulas or bot Δ.toList

/-- Encode a sequent by the kernel's conjunction, implication, and disjunction. -/
noncomputable def sequentToFormula (Γ Δ : Finset Expr) : Expr :=
  if Γ = ∅ then disjunction Δ else imp (conjunction Γ) (disjunction Δ)

noncomputable def sequentLeq (leq : ExprRel) (Γ Δ Γ' Δ' : Finset Expr) : Prop :=
  leq (sequentToFormula Γ Δ) (sequentToFormula Γ' Δ')

/-- Congruence needed by the proof-system correspondence: equality of individual
terms and implication (the encoding of sequents).

Congruence for other logical constructors could be added, but is not needed:
larger contexts are handled using cut and structural weakening.
-/
class RelationCongruence (leq : ExprRel) : Prop where
  eq_congr : ∀ {s s' t t'}, isTerm s → isTerm s' → isTerm t → isTerm t' →
    isSame leq s s' → isSame leq t t' → isSame leq (eq s t) (eq s' t')
  imp_congr : ∀ {p p' q q'}, isSame leq p p' → isSame leq q q' →
    isSame leq (imp p q) (imp p' q')

/-- Convenience bundle of a preorder and constructor congruence.

The Ordered–Weakened correspondence only needs reflexivity and congruence;
this bundle additionally supplies transitivity for consumers that need it.
-/
class ProofOrder (leq : ExprRel) extends IsPreorder Expr leq,
    RelationCongruence leq

/-- Bundle the structural translation assumptions without an algebraic carrier. -/
@[reducible] def ProofOrder.of (leq : ExprRel) [IsPreorder Expr leq]
    [RelationCongruence leq] :
    ProofOrder leq where
  refl := fun p => Std.Refl.refl p
  trans := fun p q r => IsTrans.trans p q r
  toRelationCongruence := inferInstance

namespace OrderLaws

@[simp] theorem self_le {leq : ExprRel} [Std.Refl leq] (p : Expr) : leq p p :=
  Std.Refl.refl p

theorem transitive {leq : ExprRel} [IsTrans Expr leq] {p q r : Expr}
    (h₁ : leq p q) (h₂ : leq q r) : leq p r :=
  IsTrans.trans p q r h₁ h₂

theorem same_symm {leq : ExprRel} {p q} (h : isSame leq p q) : isSame leq q p := ⟨h.2, h.1⟩

theorem same_trans {leq : ExprRel} [IsTrans Expr leq] {p q r}
    (h : isSame leq p q) (k : isSame leq q r) : isSame leq p r :=
  ⟨transitive h.1 k.1, transitive k.2 h.2⟩

end OrderLaws

theorem RelationCongruence.refl_eq {leq : ExprRel} [Std.Refl leq]
    [RelationCongruence leq] {s t : Expr} (hs : isTerm s) (ht : isTerm t)
    (h : isSame leq s t) : isSame leq (eq s s) (eq s t) :=
  RelationCongruence.eq_congr hs hs hs ht
    ⟨OrderLaws.self_le s, OrderLaws.self_le s⟩ h

theorem containedExcept_of_sdiff {leq : ExprRel} [Std.Refl leq]
    {Γ Δ : Finset Expr} {p : Expr}
    (h : ∀ q ∈ Γ \ Δ, isSame leq p q) : containedExcept leq Γ Δ p := by
  intro q hq
  by_cases hΔ : q ∈ Δ
  · exact Or.inl ⟨q, hΔ, OrderLaws.self_le q, OrderLaws.self_le q⟩
  · have heq := h q (Finset.mem_sdiff.mpr ⟨hq, hΔ⟩)
    exact Or.inr ⟨heq.2, heq.1⟩

theorem containedExceptEither_of_sdiff {leq : ExprRel} [Std.Refl leq]
    {Γ Δ : Finset Expr} {p q : Expr}
    (h : ∀ r ∈ Γ \ Δ, isSame leq p r ∨ isSame leq q r) :
    containedExceptEither leq Γ Δ p q := by
  intro r hr
  by_cases hΔ : r ∈ Δ
  · exact Or.inl ⟨r, hΔ, OrderLaws.self_le r, OrderLaws.self_le r⟩
  · rcases h r (Finset.mem_sdiff.mpr ⟨hr, hΔ⟩) with hp | hq
    · exact Or.inr (Or.inl ⟨hp.2, hp.1⟩)
    · exact Or.inr (Or.inr ⟨hq.2, hq.1⟩)

theorem setLeq_of_subset {leq : ExprRel} [Std.Refl leq]
    {Γ Δ : Finset Expr} (h : Γ ⊆ Δ) : setLeq leq Γ Δ :=
  fun p hp => ⟨p, h hp, OrderLaws.self_le p, OrderLaws.self_le p⟩
