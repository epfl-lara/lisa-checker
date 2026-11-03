import Lisa.Lambda.AlphaBetaEta

/-! Keep capture-free syntax and conversion independent of named expressions and NbE. -/

namespace Lisa.Tests.LambdaCore

open Lambda

run_cmd do
  let env ← Lean.getEnv
  for name in [`Lisa.Expr, `Lisa.AlphaBetaEta, `Lisa.Lambda.eval] do
    if env.contains name then
      throwError "Intrinsic lambda core imports {name}"

private def identity : Term (prop >> prop) := .lam prop (.bound 0)
private def argument : Term prop := .free ⟨"p", 0⟩

example : Equiv (.app identity argument) argument := .beta _ _

example (σ : Sub) {p q : Term s} (h : Equiv p q) :
    Equiv (p.subst σ) (q.subst σ) := h.subst σ

example (p : Term t) (q : Term s) :
    (p.shift s).instantiate q = p := p.shift_instantiate q

end Lisa.Tests.LambdaCore
