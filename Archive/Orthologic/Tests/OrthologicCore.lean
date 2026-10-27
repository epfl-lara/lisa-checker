import Lisa.Orthologic.Free

/-! Keep the complete normalizing OL engine independent of Lisa syntax and reference search. -/

namespace Lisa.Tests.OrthologicCore

open Orthologic

run_cmd do
  let env ← Lean.getEnv
  for name in [`Lisa.Expr, `CheckerOrder, `Lisa.Orthologic.Reference.probe,
      `Lisa.Orthologic.Calculus.Reference.saturate] do
    if env.contains name then
      throwError "Pure orthologic core imports {name}"

private structure Atom where
  index : Nat
  deriving DecidableEq

private def a : Nnf Atom := .lit ⟨0⟩ false
private def b : Nnf Atom := .lit ⟨1⟩ false

#guard Calculus.decideLe (.meet a b) a
#guard !Calculus.decideLe a b
#guard decide (Calculus.value (.meet a b) ≤ Calculus.value a)
#guard decide (Calculus.value (.meet a b) = Calculus.value (.meet b a))

example {α : Type} [DecidableEq α] (p q : Nnf α) :
    Calculus.decideLe p q = true ↔ Calculus.Derives p q :=
  Calculus.decideLe_iff p q

end Lisa.Tests.OrthologicCore
