import Lisa.Ordered

/-! Regression checks for the parameters of general pointwise substitution. -/
namespace SubstitutionRuleTests
open Lisa Expr

private def a : SVar := ⟨⟨"a", 0⟩, ind⟩
private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def u : SVar := ⟨⟨"u", 0⟩, ind⟩
private def v : SVar := ⟨⟨"v", 0⟩, ind⟩
private def p : SVar := ⟨⟨"p", 0⟩, prop⟩
private def f : SVar := ⟨⟨"f", 0⟩, ind >> ind⟩

-- The parameter must be independent of the compared expressions, not just
-- fresh for the other formulas of the comparison premise.
private def identityConstant : SubstPair := ⟨.lam u (.var u), .lam u (.var a)⟩
example : identityConstant.validParams [x] := by decide
example : ¬ identityConstant.validParams [a] := by decide

-- Testing two functions only on the diagonal does not establish equality.
private def projections : SubstPair :=
  ⟨.lam u (.lam v (.var u)), .lam u (.lam v (.var v))⟩
example : projections.validParams [a, x] := by decide
example : ¬ projections.validParams [a, a] := by decide
example : ¬ projections.validParams [a] := by decide
example : ¬ projections.validParams [a, x, u] := by decide
example : ¬ projections.validParams [a, p] := by decide

-- Proposition and function arguments are allowed without object-language
-- quantification over those sorts.
private def propositional : SubstPair := ⟨.lam p (.var p), .lam p (and (.var p) top)⟩
private def functional : SubstPair := ⟨.lam f (.var f), .lam f (.var f)⟩
example : propositional.validParams [p] := by decide
example : functional.validParams [f, x] := by decide
example : isFormula (propositional.pointwiseEq [p]) :=
  SubstPair.pointwiseEq_isFormula (by decide)
example : isFormula (functional.pointwiseEq [f, x]) :=
  SubstPair.pointwiseEq_isFormula (by decide)

-- Ground comparisons need no parameters, but still require matching sorts.
example : (SubstPair.mk (.var a) (.var x)).validParams [] := by decide
example : (SubstPair.mk (.var p) top).validParams [] := by decide
example : ¬ (SubstPair.mk (.var a) (.var p)).validParams [] := by decide
example : (SubstPair.mk (.var a) (.var x)).pointwiseEq [] = eq (.var a) (.var x) := rfl
example : (SubstPair.mk (.var p) top).pointwiseEq [] = iff (.var p) top := rfl

end SubstitutionRuleTests
