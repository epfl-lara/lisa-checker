import Lisa.AlphaBetaEtaNormalization.AlphaBetaEta

namespace Lisa.AlphaBetaEtaNormalization.Tests
run_cmd do
  let env ← Lean.getEnv
  for name in [`Lisa.Expr, `Lisa.AlphaBetaEta, `Lisa.AlphaBetaEtaNormalization.eval] do
    if env.contains name then throwError "Syntax/conversion imports {name}"

example (e : Term t) (a : Term s) : (e.shift s).instantiate a = e := e.shift_instantiate a
example (σ : Sub) (h : Equiv p q) : Equiv (p.subst σ) (q.subst σ) := h.subst σ
example : Equiv (.app (.lam prop (.bound 0)) (.free ⟨"p", 0⟩)) (.free ⟨"p", 0⟩ : Term prop) := .beta _ _
end Lisa.AlphaBetaEtaNormalization.Tests
