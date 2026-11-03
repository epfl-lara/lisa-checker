import Lisa.Checker.ProofRelation

open Lisa Expr

namespace AlphaBetaEtaOrderTests

def x : SVar := ⟨⟨"x", 0⟩, ind⟩
def y : SVar := ⟨⟨"y", 0⟩, ind⟩
def z : SVar := ⟨⟨"z", 0⟩, ind⟩
def g : Expr := .const (.named "g" (ind >> ind))
def a : Expr := .const (.named "a" ind)
def p : Expr := .const (.named "p" prop)
def q : Expr := .const (.named "q" prop)

-- Alpha comparison preserves free names, binder depth, shadowing, and sorts.
#guard AlphaEq (.lam x (.var x)) (.lam y (.var y))
#guard AlphaEq (.lam x (.lam x (.var x))) (.lam y (.lam z (.var z)))
#guard !(AlphaEq (.lam x (.var y)) (.lam y (.var y)))
#guard !(AlphaEq (.lam x (.lam y (.var x))) (.lam y (.lam z (.var z))))
#guard !(AlphaEq (.lam x p) (.lam ⟨x.id, prop⟩ p))
#guard !(AlphaEq (.var x) (.var ⟨x.id, prop⟩))

example : AlphaBetaEta (.lam x (.var x)) (.lam y (.var y)) := .alpha (by decide)

-- Substitution must rename the binder instead of capturing the argument.
def captureBody : Expr := .lam y (.var x)
def captureResult : Expr := substOne x (.var y) captureBody

#guard AlphaEq captureResult (.lam z (.var y))
#guard !(AlphaEq captureResult (.lam y (.var y)))

example : AlphaBetaEta (.app (.lam x captureBody) (.var y)) captureResult :=
  .beta x captureBody (.var y) rfl

-- Eta requires a fresh binder and the correct arrow domain.
example : AlphaBetaEta (.lam x (.app g (.var x))) g :=
  .eta x g ind rfl (by decide)

#guard x ∈ (Expr.app (.const (.named "h" (ind >> ind >> ind))) (.var x)).freeVars
#guard !(g.sort = some (prop >> ind))
#guard !(p.sort = some x.sort)

-- Beta can expose an eta redex; conversion must include the resulting equation.
def delayed : Expr := .lam x (.app (.lam z (.var z)) (.app g (.var x)))

theorem beta_then_eta : AlphaBetaEta delayed g := by
  have hb : AlphaBetaEta (.app (.lam z (.var z)) (.app g (.var x)))
      (.app g (.var x)) := by
    exact AlphaBetaEta.beta z (.var z) (.app g (.var x)) rfl
  exact (AlphaBetaEta.lam x hb).trans (.eta x g ind rfl (by decide))

example : AlphaBetaEta.term delayed = AlphaBetaEta.term g :=
  AlphaBetaEta.term_eq.mpr beta_then_eta

example : AlphaBetaEta.termSort (AlphaBetaEta.term delayed) = some (ind >> ind) := rfl

-- Alpha-beta-eta conversions are included in the checker's proof relation.
example : Imported.Checker.ProofRelation delayed g :=
  Imported.Checker.ProofRelation.of_alphaBetaEta beta_then_eta

example : Imported.Checker.ProofRelation
    (.app (.const (.named "P" ((ind >> ind) >> prop))) delayed)
    (.app (.const (.named "P" ((ind >> ind) >> prop))) g) :=
  Imported.Checker.ProofRelation.of_alphaBetaEta (.app (.refl _) beta_then_eta)

#print axioms AlphaBetaEta.preserves_sort
#print axioms beta_then_eta
#print axioms Imported.Checker.ProofRelation.of_alphaBetaEta

end AlphaBetaEtaOrderTests
