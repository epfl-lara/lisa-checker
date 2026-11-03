# lisa-checker

An implementation of a proof checker for Lisa's core λFOL logic.

The executable checker uses αβη canonicalization followed by extended orthologic
normalization and comparison, with verified memoization and soundness in
`Ordered AlphaBetaEta`.

```console
lake build Lisa lisa-checker Tests
lake exe lisa-checker [--limit N] [--closed] [--trace] PREFIX|DIRECTORY ...
```

See the [project walkthrough](Lisa/WALKTHROUGH.md),
[checker guide](Lisa/Checker/README.md), and
[orthologic package guide](Lisa/Orthologic/README.md).
The previous OL implementation is retained for reference in
[Archive/Orthologic](Archive/Orthologic/README.md), outside the active build.

The conservativity development is in [Lisa/LambdaFol](Lisa/LambdaFol.lean).
The [final theorem](Lisa/LambdaFol/Statements.lean), `ordered_iff_pureFol`, proves that
`Ordered AlphaBetaEta` and independent first-order logic with epsilon prove the
same sequents under the first-order conclusion restrictions. Both directions are syntactic proof translations;
intermediate source formulas may contain higher-order symbols.
[Expression representation](Lisa/LambdaFol/ToPureFol/PureFolToOrdered/Equivalence.lean)
also proves that the canonical PureFol translation embeds back to an αβη-equivalent expression.
The forward proof follows **Ordered → LambdaFol → WithoutInstantiation → PureFol**: pass to αβη formula
classes, eliminate schematic instantiation, then replace higher-order symbols and normalize.
WithoutInstantiation and LambdaFol retain generalized replacement and epsilon; only LambdaFol has instantiation. Their
[equivalence theorems](Lisa/LambdaFol/Statements.lean) use the
same independent target.

The [reduction guide](Lisa/LambdaFol/README.md) explains the conclusion restrictions,
the shared `Syntax`, the calculi (`ProofSystem`, `WithoutInstantiation`, `PureFol`),
and the final `Statements`. Supporting proofs live in `FromOrdered`,
`EliminateInstantiation`, and `ToPureFol`. PureFol uses the same free identifiers
as Lisa and retains epsilon; assumptions are sequent antecedents. The proof translations are syntactic.

