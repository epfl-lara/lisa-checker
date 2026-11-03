import Lisa.Combined.Reference
import Lisa.Combined.Propositional

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

-- The concrete reference order supplies the existing algebra API.
example : isSame ExpressionOrder.leq delayed g :=
  ExpressionOrder.same_of_alphaBetaEta beta_then_eta

example : isSame ExpressionOrder.leq
    (.app (.const (.named "P" ((ind >> ind) >> prop))) delayed)
    (.app (.const (.named "P" ((ind >> ind) >> prop))) g) :=
  ExpressionOrder.same_of_alphaBetaEta (.app (.refl _) beta_then_eta)

example : isSame ExpressionOrder.leq (and p top) p := by
  apply ExpressionOrder.interpretation.same_iff.mpr
  simp [ExpressionOrder.interpretation.and_eq, ExpressionOrder.interpretation.top_eq]

example : isSame ExpressionOrder.leq (and p (neg p)) bot := by
  apply ExpressionOrder.interpretation.same_iff.mpr
  simp [ExpressionOrder.interpretation.and_eq, ExpressionOrder.interpretation.neg_eq, ExpressionOrder.interpretation.bot_eq]

example : isSame ExpressionOrder.leq (eq a a) top :=
  ⟨.top _, .eqRefl a rfl⟩

example : isSame ExpressionOrder.leq (eq a (.var x)) (eq (.var x) a) :=
  ⟨.eqSymm _ _ rfl rfl, .eqSymm _ _ rfl rfl⟩

example : ExpressionOrder.leq (forall_ x (and p q)) (forall_ x p) :=
  .forallMono x rfl rfl rfl (.meetLeft _ _)

example (φ ψ : Expr) (h : Lisa.Orthologic.checkExprLe φ ψ = true) :
    ExpressionOrder.leq φ ψ := Lisa.Orthologic.checkExprLe_sound ExpressionOrder.interpretation φ ψ h

example (φ : Expr) :
    ExpressionOrder.ofTerm (AlphaBetaEta.term φ) = ExpressionOrder.value φ := rfl

#print axioms AlphaBetaEta.preserves_sort
#print axioms beta_then_eta
#print axioms ExpressionOrder.instOrtholatticeCarrier
#print axioms ExpressionOrder.instIsPreorderExprLeq

end AlphaBetaEtaOrderTests
