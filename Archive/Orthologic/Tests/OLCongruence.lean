import Lisa.AlphaBetaEtaOrder
import Lisa.Lambda.NamedDecision

/-! A certified higher-order substitution example for the OL reorganization,
along with checks distinguishing it from alpha-beta-eta conversion. -/
namespace OLCongruenceTests
open Lisa Expr

def x : SVar := ⟨⟨"x", 0⟩, prop⟩
def p : SVar := ⟨⟨"p", 0⟩, prop⟩
def h : SVar := ⟨⟨"h", 0⟩, (prop >> prop) >> prop⟩
def f : Expr := .lam x (and (.var x) top)
def g : Expr := .lam x (.var x)

example : isFormula (.app (.var h) f) := rfl
example : isFormula (.app (.var h) g) := rfl

-- The body comparison is available in the baseline proof system.
def bodyForward : Ordered.ProofTree AlphaBetaEta {and (.var x) top} {.var x} := by
  have hp : isFormula (.var x) := rfl
  have ht : isFormula top := rfl
  have w := Ordered.ProofTree.weakening
    (leq := AlphaBetaEta) (Γ := {Expr.var x}) (Δ := {Expr.var x})
    (Γ' := insert (.var x) (insert top ∅)) (Δ' := {Expr.var x})
    (by simpa [isFSet] using hp) (by simpa [isFSet] using hp)
    (by simp [isFSet, x, top, Expr.sort]) (by simpa [isFSet] using hp)
    (.hypothesis _ hp) (by simp) (by simp)
  simpa using Ordered.ProofTree.leftAnd (Γ := ∅) (Δ := {.var x})
    (.var x) top (by simp [isFSet]) (by simpa [isFSet] using hp) hp ht w

-- The reverse body comparison also has a derivation.
def bodyBackward : Ordered.ProofTree AlphaBetaEta {.var x} {and (.var x) top} := by
  have hp : isFormula (.var x) := rfl
  simpa using Ordered.ProofTree.rightAnd
    (leq := AlphaBetaEta) (Γ := {.var x}) (Δ := ∅) (Ω := ∅) (Ξ := ∅)
    (.var x) top (by simpa [isFSet] using hp) (by simp [isFSet])
    (by simp [isFSet]) (by simp [isFSet]) hp (show isFormula top from rfl)
    (by simpa using Ordered.ProofTree.hypothesis (leq := AlphaBetaEta) (.var x) hp)
    (by simpa using (Ordered.ProofTree.rightTrue (leq := AlphaBetaEta)))

-- Alpha-beta-eta conversion alone does not perform this logical simplification.
example : ¬ AlphaBetaEta (.app (.var h) f) (.app (.var h) g) := by
  intro heq
  have hn := (Lambda.alphaBetaEta_iff_normalizeNamed_eq
    (s := prop) (p := .app (.var h) f) (q := .app (.var h) g) rfl).mp heq
  have hne : Lambda.normalizeNamed (.app (.var h) f) ≠
      Lambda.normalizeNamed (.app (.var h) g) := by decide
  exact hne hn

private def z : SVar := ⟨⟨"z", 0⟩, prop >> prop⟩
private def replacement : SubstRule :=
  ⟨[(⟨f, g⟩, [x])], ⟨[z], iff (.app (.var h) f) (.app (.var h) (.var z))⟩⟩

private def iffSelf (e : Expr) (he : isFormula e) :
    Ordered.ProofTree AlphaBetaEta ∅ {iff e e} := by
  have hi : Ordered.ProofTree AlphaBetaEta ∅ {imp e e} :=
    .rightImp (Γ := ∅) (Δ := ∅) e e (by simp) (by simp) he he (.hypothesis e he)
  simpa using Ordered.ProofTree.rightIff (Γ := ∅) (Ω := ∅) (Δ := ∅) (Ξ := ∅)
    e e (by simp) (by simp) (by simp) (by simp) he he hi hi

/-- The general rule proves the higher-order congruence required by OL normalization. -/
def applicationCongruence : Ordered.ProofTree AlphaBetaEta ∅
    {iff (.app (.var h) f) (.app (.var h) g)} := by
  have hp : isFormula (.var x) := rfl
  have hpt : isFormula (and (.var x) top) := rfl
  have forward : Ordered.ProofTree AlphaBetaEta ∅ {imp (and (.var x) top) (.var x)} :=
    .rightImp (Γ := ∅) (Δ := ∅) _ _ (by simp) (by simp) hpt hp bodyForward
  have backward : Ordered.ProofTree AlphaBetaEta ∅ {imp (.var x) (and (.var x) top)} :=
    .rightImp (Γ := ∅) (Δ := ∅) _ _ (by simp) (by simp) hp hpt bodyBackward
  have eqBody : Ordered.ProofTree AlphaBetaEta ∅ {iff (and (.var x) top) (.var x)} := by
    simpa using Ordered.ProofTree.rightIff (Γ := ∅) (Ω := ∅) (Δ := ∅) (Ξ := ∅)
      _ _ (by simp) (by simp) (by simp) (by simp) hpt hp forward backward
  have conversion : AlphaBetaEta (iff (and (.var x) top) (.var x)) replacement.equation := by
    exact .app (.app (.refl _) (.symm (.beta x (and (.var x) top) (.var x) rfl)))
      (.symm (.beta x (.var x) (.var x) rfl))
  have compared : Ordered.ProofTree AlphaBetaEta ∅ {replacement.equation} :=
    .restateWeaken (by simp) (isFSet_insert (isFormula_iff hpt hp) isFSet_empty)
      (by simp) (isFSet_insert (SubstRule.equation_isFormula (r := replacement) (by decide)) isFSet_empty)
      eqBody (by simpa [sequentLeq, sequentToFormula, disjunction, foldFormulas] using conversion)
  have start : Ordered.ProofTree AlphaBetaEta ∅ {replacement.source} :=
    iffSelf (.app (.var h) f) rfl
  simpa using Ordered.ProofTree.rightSubst
    (Γ := ∅) (Δ := ∅) (Θ := ∅) (Ξ := ∅) replacement
    (by simp) (by simp) (by simp) (by simp) (by decide) (by decide) start compared

#print axioms applicationCongruence

-- Substitution into λx. p does not bind the x introduced by the replacement.
example : x ∈ (substOne p (and (.var x) top) (.lam x (.var p))).freeVars := by
  decide

end OLCongruenceTests
