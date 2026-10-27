import Tests.CheckerModel
import Lisa.OrderedWeakened
import Lisa.OrderedComparison
import Lisa.AlphaBetaEtaOrder
import Lisa.Combined.Reference
import Lisa.Combined.Propositional

open Lisa Expr Imported Imported.Checker

namespace OrderRequirementsTests

-- Two-formula admissibility needs no order laws on the target relation.
private def equalityAdmissible (target : ExprRel) : Ordered.Admissible Eq target := by
  intro a b ha _ h
  subst b
  exact .hypothesis a ha

noncomputable example {target : ExprRel} {Γ Δ : Finset Expr}
    (p : Ordered.ProofTree Eq Γ Δ) : Ordered.ProofTree target Γ Δ :=
  Ordered.translate (equalityAdmissible target) p

-- Empty contexts use the explicit falsehood and truth rules during encoding.
noncomputable example (target : ExprRel) :
    Ordered.ProofTree target ∅ {sequentToFormula {bot} ∅} :=
  Ordered.packSequent (by simp [isFSet, isFormula, hasSort, Expr.bot])
    (by simp [isFSet]) .leftFalse

noncomputable example (target : ExprRel) :
    Ordered.ProofTree target {sequentToFormula ∅ ∅} ∅ := by
  simpa using (Ordered.useSequentFormula (r := target) (Γ := ∅) (Δ := ∅)
    (by simp [isFSet]) (by simp [isFSet]))

-- The conversion baseline embeds in the generated reference relation.
example {Γ Δ : Finset Expr} (proof : Ordered.AlphaBetaEtaProof Γ Δ) :
    Ordered.ProofTree ExpressionOrder.leq Γ Δ :=
  Ordered.mapOrder (fun h => (ExpressionOrder.same_of_alphaBetaEta h).1) proof

-- AlphaBetaEta is available in the baseline, including inside sequent encodings.
example {p q : Expr} (hp : isFormula p) (hq : isFormula q) (h : AlphaBetaEta p q) :
    Ordered.AlphaBetaEtaProof {p} {q} := by
  refine .restateWeaken (by simpa [isFSet] using hp) (by simpa [isFSet] using hp)
    (by simpa [isFSet] using hp) (by simpa [isFSet] using hq) (.hypothesis p hp) ?_
  simpa [sequentLeq, sequentToFormula, conjunction, disjunction, foldFormulas, Expr.imp]
    using (AlphaBetaEta.app (AlphaBetaEta.refl (.app (.const (.named "imp" (prop >> prop >> prop))) p)) h)

-- Equivalence to the richer reference instance still requires reverse admissibility.
example (h : Ordered.Admissible ExpressionOrder.leq AlphaBetaEta) (Γ Δ : Finset Expr) :
    Nonempty (Ordered.AlphaBetaEtaProof Γ Δ) ↔
      Nonempty (Ordered.ProofTree ExpressionOrder.leq Γ Δ) :=
  Ordered.provable_iff_of_simulation
    (fun h => (ExpressionOrder.same_of_alphaBetaEta h).1) h Γ Δ

example {leq : ExprRel} (hΓ : isFSet Γ) (hΔ : isFSet Δ) (htop : top ∈ Δ) :
    Ordered.ProofTree leq Γ Δ :=
  .weakening (by simp [isFSet]) (by simp [isFSet, Expr.top]) hΓ hΔ
    .rightTrue (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr htop)

-- Public consumers use named bundles; none assumes an ortholattice.
example {leq : ExprRel} [CheckerOrder leq] (proof : LinearProof) (target : Statement) :
    Except CheckError (ClosedChecked leq target) :=
  checkClosed proof target

example {leq : ExprRel} [ProofOrder leq] (Γ Δ : Finset Expr) :
    Nonempty (Ordered.ProofTree leq Γ Δ) ↔ Nonempty (Weakened.ProofTree leq Γ Δ) :=
  ordered_eq_weakened leq Γ Δ

example {leq : ExprRel} [Std.Refl leq] {Γ Δ ss}
    (imports : ∀ s ∈ ss, Nonempty (Weakened.ProofTree leq s.1 s.2)) :
    Nonempty (Imported.ProofTree leq Γ Δ ss) ↔ Nonempty (Weakened.ProofTree leq Γ Δ) :=
  Imported.withAssumptions_iff imports

-- Rebundling must retain local decisions and reducers, not a backend's defaults.
example {leq : ExprRel} [CheckerOrder leq] (decision : DecidableRel leq) :
    letI := decision
    (CheckerOrder.of leq).decision = decision := rfl

example {leq : ExprRel} [CheckerOrder leq] (reduction : OrderReduction leq) :
    letI := reduction
    (CheckerOrder.of leq).toOrderReduction.reduce = reduction.reduce := rfl

-- The generated lambda/OL reference order supplies the stronger translation bundle.
section Reference

local instance : ProofOrder ExpressionOrder.leq := ProofOrder.of _

example (Γ Δ : Finset Expr) :
    Nonempty (Ordered.ProofTree ExpressionOrder.leq Γ Δ) ↔
      Nonempty (Weakened.ProofTree ExpressionOrder.leq Γ Δ) :=
  ordered_eq_weakened _ Γ Δ

end Reference

-- These signatures fail to elaborate if an algebra dependency is reintroduced.
example {leq : ExprRel} [SequentEncoding leq] [OrderReduction leq] [DecidableRel leq]
    (proof : LinearProof) (target : Statement) :
    Except CheckError (ClosedChecked leq target) :=
  letI := CheckerOrder.of leq
  checkClosed proof target

noncomputable example {leq : ExprRel} {Γ Δ ss}
    (proof : Imported.ProofTree leq Γ Δ ss)
    (imports : ∀ s ∈ ss, Weakened.ProofTree leq s.1 s.2) :
    Weakened.ProofTree leq Γ Δ :=
  Imported.resolve proof imports

example {leq : ExprRel} [Std.Refl leq] {Γ Δ}
    (proof : Ordered.ProofTree leq Γ Δ) : Weakened.ProofTree leq Γ Δ :=
  orderedToWeakened proof

noncomputable example {source target : ExprRel} {Γ Δ}
    (h : Ordered.Admissible source target)
    (proof : Ordered.ProofTree source Γ Δ) : Ordered.ProofTree target Γ Δ :=
  Ordered.translate h proof

example {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq] (Γ Δ) :
    Nonempty (Ordered.ProofTree leq Γ Δ) ↔ Nonempty (Weakened.ProofTree leq Γ Δ) :=
  ordered_eq_weakened leq Γ Δ

example {leq : ExprRel} [Std.Refl leq]
    {Γ Δ ss} (imports : ∀ s ∈ ss, Nonempty (Weakened.ProofTree leq s.1 s.2)) :
    Nonempty (Imported.ProofTree leq Γ Δ ss) ↔ Nonempty (Weakened.ProofTree leq Γ Δ) :=
  Imported.withAssumptions_iff imports

example {leq : ExprRel} [OrderReduction leq]
    (p q : Expr) (h : reducedSame leq p q) : isSame leq p q :=
  OrderReduction.sound p q h

private def a : Expr := .const (.named "A" prop)
private def b : Expr := .const (.named "B" prop)

/-- Compare adjacent tags to test checking without transitivity or an algebra.

This relation is deliberately not a logical semantics. An Imported certificate
for a supplied relation must not be confused with a proof of FOL soundness.
-/
private def tag (p : Expr) : Nat :=
  if CheckerModel.value 0 p then
    if CheckerModel.value 1 p then 2 else 1
  else 0

private def near (p q : Expr) : Prop :=
  tag p ≤ tag q + 1 ∧ tag q ≤ tag p + 1

private instance : DecidableRel near := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

private instance : OrderReduction near where
  reduce := id
  preserves := fun p => by simp [isSame, near]
  preservesSort := fun _ => rfl
  reflect p q h := by cases h; simp [isSame, near]

private theorem tag_encoding (pre post : List Expr) :
    tag (listSequentToFormula pre post) =
      tag (sequentToFormula pre.toFinset post.toFinset) := by
  have h := CheckerModel.interpretation.listSequent pre post
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  change CheckerModel.value 0 _ = CheckerModel.value 0 _ at h₀
  change CheckerModel.value 1 _ = CheckerModel.value 1 _ at h₁
  simp only [tag, h₀, h₁]

private instance : SequentEncoding near where
  compare := by
    intro pre post p
    simp only [near, tag_encoding, iff_self, and_self]

private instance : CheckerOrder near := CheckerOrder.of _

example : ¬ IsTrans Expr near := by
  intro h
  have h₀ : near bot (neg a) := by decide
  have h₁ : near (neg a) top := by decide
  have h₂ : ¬ near bot top := by decide
  exact h₂ (h.trans _ _ _ h₀ h₁)

-- The checker elaborates and runs without a preorder, weakening or truth law.
#eval show IO Unit from do
  let proof : LinearProof := #[⟨⟨[a], [a]⟩, .hypothesis a⟩]
  match checkClosed (leq := near) proof ⟨[a], [a]⟩ with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"minimal-interface check failed: {repr e}")

-- Exercise both comparison directions, permutations, duplicates and empty sides.
#eval show IO Unit from do
  let statements : List Statement :=
    [⟨[], []⟩, ⟨[], [top]⟩, ⟨[], [a, b, a]⟩, ⟨[], [b, a]⟩,
      ⟨[a, b, a], [a, b]⟩, ⟨[b, a], [b, a, a]⟩,
      ⟨[a, a], []⟩, ⟨[a], []⟩]
  for s in statements do
    for t in statements do
      letI := Statement.decideLeq (leq := CheckerModel.leq) s t
      unless decide (sequentLeq CheckerModel.leq
          s.sequent.1 s.sequent.2 t.sequent.1 t.sequent.2) =
          decide (CheckerModel.leq s.formula t.formula) do
        throw (IO.userError "whole-sequent comparison changed during encoding")
    letI := Statement.decideTrue (leq := CheckerModel.leq) s
    unless decide (isSame CheckerModel.leq (sequentToFormula s.sequent.1 s.sequent.2) top) =
        decide (isSame CheckerModel.leq s.formula top) do
      throw (IO.userError "truth comparison changed during encoding")
  let proof : LinearProof := #[
    ⟨⟨[a, b, a], [a, b]⟩, .assume⟩,
    ⟨⟨[b, a], [b, a, a]⟩, .hypothesis a⟩,
    ⟨⟨[a, b], [a, b]⟩, .discharge 0 1⟩]
  match checkClosed (leq := CheckerModel.leq) proof ⟨[b, a], [b, a]⟩ with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"reordered discharge failed: {repr e}")

#print axioms OrderReduction.sound
#print axioms Imported.Checker.checkClosed
#print axioms ordered_eq_weakened
#print axioms Imported.withAssumptions_iff

end OrderRequirementsTests
