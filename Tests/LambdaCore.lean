import Lisa.Lambda.Conversion

/-! Keep capture-free syntax and conversion independent of named expressions and NbE. -/

namespace Lisa.Tests.LambdaCore

open Lambda

run_cmd do
  let env ← Lean.getEnv
  for name in [`Lisa.Expr, `Lisa.Conversion, `Lisa.Lambda.eval] do
    if env.contains name then
      throwError "Intrinsic lambda core imports {name}"

private def identity : Term [] (prop >> prop) := .lam (.bound .here)
private def argument : Term [] prop := .free ⟨"p", 0⟩

example : Equiv (.app identity argument) argument := .beta _ _

example (σ : Sub Γ Δ) {p q : Term Γ s} (h : Equiv p q) :
    Equiv (p.subst σ) (q.subst σ) := h.subst σ

example (p : Term Γ t) (q : Term Γ s) :
    (p.rename Var.there).instantiate q = p := p.shift_instantiate q

end Lisa.Tests.LambdaCore
