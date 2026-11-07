import Lisa.LambdaFol.Statements

/-!
LambdaFOL proof systems and syntactic equivalence with first-order logic retaining epsilon.

* `LambdaFol/Syntax.lean`: shared formula classes modulo αβη.
* `LambdaFol/ProofSystem.lean`: the full calculus.
* `LambdaFol/WithoutInstantiation.lean`: the calculus without schematic instantiation.
* `LambdaFol/PureFol.lean`: independent first-order syntax and inference rules.
* `LambdaFol/FirstOrder.lean`: restrictions on concluding expressions.
* `LambdaFol/Translation.lean`: their canonical first-order translation.
* `LambdaFol/Statements.lean`: the final equivalence theorems.

The proof stages are `FromOrdered/`, `EliminateInstantiation/`, and `ToPureFol/`.
Only the concluding sequent must satisfy the first-order restrictions.
See `LambdaFol/README.md` for reading routes and the dependency-ordered file inventory.
-/
