import Lisa.CombinedCached

/-! Guard the production checker's dependencies and exact frontend/cache refinements. -/

namespace Lisa.Tests.CombinedCore

run_cmd do
  let env ← Lean.getEnv
  for name in [`Lisa.Orthologic.Reference.probe,
      `Lisa.Orthologic.Calculus.Reference.saturate,
      `Lisa.Lambda.Normal, `Lisa.Lambda.Propositional.check] do
    if env.contains name then
      throwError "Combined checker imports optional theory {name}"

example (p : Expr) :
    Lambda.normalizeNamed p =
      (Lambda.elaborate [] (p.toNameless [])).map
        (fun ⟨_, e⟩ => (Lambda.normalize e).reify Lambda.Context.empty) :=
  Lambda.normalizeNamed_eq p

example (config : Orthologic.Nnf.MemoConfig) (budget : Nat) (p q : Expr) :
    Combined.Cached.check config budget p q = Combined.Replay.check budget p q :=
  Combined.Cached.check_eq config budget p q

end Lisa.Tests.CombinedCore
