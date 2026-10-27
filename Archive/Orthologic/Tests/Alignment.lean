import Lisa.OrderedComparison
import Lisa.OrderedWeakened
import Tests.OrderModel

open Lisa Expr

namespace AlignmentTests

def x : SVar := ⟨⟨"x", 0⟩, ind⟩
def x1 : SVar := ⟨⟨"x", 1⟩, ind⟩
def x2 : SVar := ⟨⟨"x", 2⟩, ind⟩
def y : SVar := ⟨⟨"y", 0⟩, ind⟩
def p : Expr := .const ⟨⟨"P", 0⟩, ind >> prop⟩
def q : Expr := .app p (.var x1)
def sigma : Subst := .cons y (.var x) .nil

example : freshId {⟨"x", 1⟩, ⟨"y", 99⟩} ⟨"x", 0⟩ = ⟨"x", 2⟩ := by decide
example : freshId ∅ ⟨"x", 10⟩ = ⟨"x", 11⟩ := by decide

-- Freshness must include the body's free variables.
example : sigma.subst (forall_ x q) = forall_ x2 q := by decide
example : x1 ∈ (sigma.subst (forall_ x q)).freeVars := by decide
example : x2 ∉ (sigma.subst (forall_ x q)).freeVars := by decide
example : sigma.subst (forall_ x q) ≠ forall_ x1 q := by decide
example : Subst.subst (.cons y (.var x) (.cons x2 (.var y) .nil))
    (forall_ x q) = forall_ ⟨⟨"x", 3⟩, ind⟩ q := by decide

-- Shadowing removes entries rather than exposing an older replacement.
example : Subst.subst (.cons x (.var y) (.cons x (.var x1) .nil))
    (.lam x (.var x)) = .lam x (.var x) := by decide
example : Subst.subst (.cons x (.var y) .nil) (.lam x (.var x)) =
    .lam x (.var x) := by decide

-- Apply replacements simultaneously, without rewriting their ranges again.
example : Subst.subst (.cons x (.var y) (.cons y (.var x1) .nil)) (.var x) =
    .var y := by decide

def context : SubstContext := ⟨[x], .app p (.var x)⟩
example : context.instantiate [.var x1] = q := by decide
example : context.instantiate [.var x1] ≠ (Expr.lam x (.app p (.var x))).applied [.var x1] :=
  by decide
example : (SubstContext.mk [x, x] (.var x)).instantiate [.var y, .var x1] =
    .var x1 := by decide
example : (SubstContext.mk [] q).instantiate [] = q := by decide
example : ¬ context.fits [] := by unfold SubstContext.fits; decide
example : ¬ context.fits [SubstPair.mk q q] := by unfold SubstContext.fits; decide
example : ¬ (SubstRule.mk [(⟨.var x, .var y⟩, [])] ⟨[x], .var x⟩).valid := by decide

def atom : Expr := .const ⟨⟨"A", 0⟩, prop⟩
example : (SubstPair.mk atom atom).pointwiseEq [] = iff atom atom := by decide
example : ((SubstPair.mk atom atom).pointwiseEq []).sort = some prop := by decide
example : (SubstPair.mk (.var x) (.var y)).pointwiseEq [] = eq (.var x) (.var y) := by decide
example : ((SubstPair.mk p p).pointwiseEq [x1]).sort = some prop := by decide
example : (SubstPair.mk p p).pointwiseEq [x1] =
    iff (.app p (.var x1)) (.app p (.var x1)) := by decide

-- Quantifier eigenvariables are checked on the whole target sequent.
example : x1 ∈ Lisa.freeVars (({q} : Finset Expr) ∪ {forall_ x1 q}) := by decide

-- Multi-premise connective rules reject an empty premise list.
example : ¬ (([] : List (AnnotatedSequent Expr)) ≠ ∅) := by simp

section ExprRel

variable {leq : ExprRel} [IsPreorder Expr leq] (m : Lisa.Orthologic.Interpretation leq) [OrderReduction leq]

-- Whole-sequent restatement must identify tautologies with different atoms.
example : sequentLeq leq {atom} {atom} {top} {top} := by
  simpa [sequentLeq, sequentToFormula, conjunction, disjunction, foldFormulas] using
    m.transitive (m.imp_self (leq := leq) atom).1
      (m.imp_self (leq := leq) top).2

-- Instantiation is constrained to the original sides, even for empty substitution.
example : ¬ setLeq leq ({atom} : Finset Expr) ∅ := by
  simp [setLeq]

-- Normalized retained contexts do not silently use the full formula order.
example {r s : Expr} (h : ¬ reducedSame leq r s) :
    ¬ reducedSubset leq {r} {s} := by
  simpa [reducedSubset] using h
example {r s a b : Expr} (h : ¬ isSame leq r s)
    (ha : ¬ isSame leq r a) (hb : ¬ isSame leq r b) :
    ¬ containedExceptEither leq {r} {s} a b := by
  simpa [containedExceptEither] using And.intro h (And.intro ha hb)

example : Nonempty (Weakened.ProofTree leq ∅ {top}) := by
  apply Nonempty.intro
  apply Weakened.ProofTree.restateTrue
  · simp
  · simp [Expr.top]
  · simp [sequentToFormula, disjunction, foldFormulas, isSame]

example (h : isSame leq (.var x) (.var y)) :
    Nonempty (Weakened.ProofTree leq ∅ {eq (.var x) (.var y)}) := by
  apply Nonempty.intro
  apply Weakened.ProofTree.rightRefl (.var x) (.var y)
  · simp
  · simp [Expr.eq, x, y]
  · rfl
  · rfl
  · exact h
  · exact ⟨_, Finset.mem_singleton_self _, ⟨m.self_le _, m.self_le _⟩⟩

example (hne : ¬ isSame leq top bot) :
    ¬ isSame leq (sequentToFormula ∅ {bot}) top := by
  simpa [sequentToFormula, disjunction, foldFormulas] using
    (fun h : isSame leq bot top => hne ⟨h.2, h.1⟩)

example (hne : ¬ isSame leq top bot) :
    OrderReduction.reduce (leq := leq) top ≠ OrderReduction.reduce (leq := leq) bot :=
  fun h => hne (OrderReduction.sound top bot h)

end ExprRel

-- Replay a nonliteral reflexivity step through strict reflexivity and restatement.
def equivalentRefl : Weakened.ProofTree AlignmentModel.leq ∅ {eq (.var x) (.var y)} :=
  Weakened.ProofTree.rightRefl (.var x) (.var y)
    (by simp) (by simp [Expr.eq, x, y]) (by rfl) (by rfl)
    (by unfold isSame AlignmentModel.leq; decide)
    ⟨_, Finset.mem_singleton_self _, ⟨AlignmentModel.interpretation.self_le _, AlignmentModel.interpretation.self_le _⟩⟩

example : (.var x : Expr) ≠ .var y := by decide
example : ¬ isSame AlignmentModel.leq (.var x) (.var x1) := by
  unfold isSame AlignmentModel.leq
  decide
example : Nonempty (Ordered.ProofTree AlignmentModel.leq ∅ {eq (.var x) (.var y)}) :=
  ⟨weakenedToOrdered equivalentRefl⟩

def removedRefl : Weakened.ProofTree AlignmentModel.leq ∅ {top} :=
  Weakened.ProofTree.leftRefl (Γ₁ := {eq (.var x) (.var y)}) (Γ₂ := {top})
    (.var x) (.var y)
    (by simp [Expr.eq, x, y]) (by simp [Expr.top])
    (Weakened.ProofTree.restateTrue
      (by simp [Expr.eq, x, y]) (by simp [Expr.top])
      (by
        simp only [sequentToFormula, Finset.singleton_ne_empty, ↓reduceIte,
          conjunction, disjunction, Finset.toList_singleton, foldFormulas, List.foldl_nil]
        exact ⟨AlignmentModel.interpretation.le_top _, AlignmentModel.interpretation.transitive (AlignmentModel.interpretation.or_right _ _)
          (AlignmentModel.interpretation.imp_same _ _).2⟩))
    (by simp) (by simp [Expr.top]) (by rfl) (by rfl)
    (by unfold isSame AlignmentModel.leq; decide)
    (setLeq_of_subset (Finset.Subset.refl _))
    (by
      intro p hp
      have h := Finset.mem_singleton.mp hp
      subst p
      exact Or.inr ⟨AlignmentModel.interpretation.self_le _, AlignmentModel.interpretation.self_le _⟩)

example : Nonempty (Ordered.ProofTree AlignmentModel.leq ∅ {top}) :=
  ⟨weakenedToOrdered removedRefl⟩

#print axioms ordered_eq_weakened
#print axioms Ordered.provable_iff
#print axioms Subst.subst_preserves_sort
#print axioms freshId_not_mem
#print axioms Lisa.Orthologic.Interpretation.sequentLeq_of_setLeq
#print axioms OrderReduction.sound
#print axioms equivalentRefl
#print axioms removedRefl

end AlignmentTests
