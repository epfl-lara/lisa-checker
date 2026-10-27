# lisa-checker

An experimental WIP implementation of a proof checker for Lisa's core λFOL logic.

The executable checker uses αβη canonicalization followed by extended orthologic
normalization and comparison, with verified memoization and soundness in
`Ordered AlphaBetaEta`.

```text
lake build Lisa lisa-checker Tests
lake exe lisa-checker [--limit N] [--closed] [--trace] PREFIX|DIRECTORY ...
```

See the [project walkthrough](Lisa/WALKTHROUGH.md),
[checker guide](Lisa/Checker/README.md), and
[orthologic implementation plan and status](Lisa/Orthologic/REORGANIZATION_PLAN.md).
The previous OL implementation is retained for reference in
[Archive/Orthologic](Archive/Orthologic/README.md), outside the active build.

The conservativity development is in [Lisa/SCLambdaToPure](Lisa/SCLambdaToPure.lean).
The [final theorem](Lisa/SCLambdaToPure/Statements.lean), `ordered_iff_pure`, proves that
`Ordered AlphaBetaEta` and independent first-order logic with epsilon prove the
same boundary sequents. Both directions are syntactic proof translations;
intermediate source formulas may contain higher-order symbols.
[Expression representation](Lisa/SCLambdaToPure/AToPure/Reverse/Equivalence.lean)
also proves that canonical readback embeds back to an αβη-equivalent expression.
The forward proof follows **Ordered → B → A → Pure**: pass to αβη formula
classes, eliminate schematic instantiation, then ground and normalize. A and B
retain generalized replacement and epsilon; only B has instantiation. Their
[boundary equivalences](Lisa/SCLambdaToPure/Statements.lean) use the
same independent target.

The [reduction guide](Lisa/SCLambdaToPure/README.md) explains the boundary,
the three entry files (`Pure`, `A`, `Statements`) and the supporting
`AToPure` and `OrderedToA` directories. Pure uses the same free identifiers
as Lisa and retains epsilon; assumptions are sequent antecedents. The package
contains one syntactic proof route, without optional model-theoretic developments.

Earlier approaches remain outside the active build in
[Archive/SCLambdaMathlib](Archive/SCLambdaMathlib) and
[Archive/SCLambdaCompleteness](Archive/SCLambdaCompleteness/README.md).
