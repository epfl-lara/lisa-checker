import Lisa.OrderedComparison
import Lisa.OrderedWeakened

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

-- Context matching remains a relation-level condition.
example {leq : ExprRel} : ¬ setLeq leq ({atom} : Finset Expr) ∅ := by
  simp [setLeq]

example {leq : ExprRel} {r s a b : Expr} (h : ¬ isSame leq r s)
    (ha : ¬ isSame leq r a) (hb : ¬ isSame leq r b) :
    ¬ containedExceptEither leq {r} {s} a b := by
  simpa [containedExceptEither] using And.intro h (And.intro ha hb)

#print axioms ordered_eq_weakened
#print axioms Ordered.provable_iff
#print axioms Subst.subst_preserves_sort
#print axioms freshId_not_mem

end AlignmentTests
