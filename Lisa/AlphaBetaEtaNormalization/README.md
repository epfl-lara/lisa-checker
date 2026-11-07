# αβη canonicalization and comparison

This package computes canonical representatives of Lisa expressions modulo
αβη-equivalence and decides that equivalence. Import
`Lisa.AlphaBetaEtaNormalization` for the public operations and guarantees.

Read **[Canonicalization.lean](Canonicalization.lean)** and
**[Comparison.lean](Comparison.lean)** first. Their signatures use Lisa's
`Expr`, sorting predicates, and `AlphaBetaEta` relation. Their operations use
[Algorithm.lean](Algorithm.lean); their theorem proofs use
[Internal/](Internal/README.md).

## Canonicalization

```lean
normalizeNamed : Expr → Option Expr
```

The result is a named expression with deterministic binder names. The operation
has no normalization fuel bound. `none` means the input is ill-sorted.

| Guarantee | Theorem |
| --- | --- |
| Failure exactly when the input's sort is `none` | `normalizeNamed_none` |
| The output is αβη-equivalent to the input | `normalizeNamed_sound` |
| The output has the same sort as the input | `normalizeNamed_sort` |
| Normalizing an output again returns that same output | `normalizeNamed_idempotent` |
| For `p.hasSort s`, `AlphaBetaEta p q` iff their normalizations are equal | `alphaBetaEta_iff_normalizeNamed_eq` |
| Alpha-equivalent inputs have identical outputs | `normalizeNamed_alpha` |

The fifth theorem is the central contract: canonical output completely
characterizes αβη-equivalence on well-sorted inputs. Its sorting premise matters:
two ill-sorted inputs both return `none`, without necessarily being equivalent.

## Comparison

```lean
compareNamed : Expr → Expr → Option Bool
```

| Result | Meaning | Theorem |
| --- | --- | --- |
| `some true` | The inputs are well-sorted and αβη-equivalent | `compareNamed_true` |
| `some false` | Both inputs are well-sorted and are not αβη-equivalent | `compareNamed_false` |
| `none` | At least one input is ill-sorted | `compareNamed_none` |

Different valid sorts give `some false`. Comparison works directly on typed
canonical forms; it does not reconstruct named output just to compare it.

`SortedExpr s` packages an `Expr` with a proof that it has sort `s`.
`SortedExpr.Equivalent` is αβη-equivalence on these expressions, with a
`DecidableRel` instance supplied by the comparison operation.

## Supporting code

The executable definitions are in **[Algorithm.lean](Algorithm.lean)**, using
the intrinsically sorted terms in [TypedSyntax.lean](TypedSyntax.lean).
Both files use the namespace `AlphaBetaEtaNormalization.Algorithm` and import
no files from `Internal`.

`Internal` is ghost code: its declarations may be used in proofs, but not in
public theorem statements or the non-erased parts of definitions. Its
[proof guide](Internal/README.md) explains correctness of evaluation, named
interpretation, and reconstruction. Proof files add lemmas to the algorithm's
namespace; the boundary is determined by their files, not their namespace names.

Orthologic uses the executable typed operations before OL normalization.
LambdaFol's translation proofs also use the typed syntax and its internal lemmas.

## Verification

```powershell
lake build Lisa lisa-checker Tests
```

[Tests/NamedDecision.lean](../../Tests/NamedDecision.lean) exercises the public
interface, including malformed inputs, differing sorts, capture avoidance,
comparison against canonical-output equality, idempotence, and decidability.
[Internal/CoreTests.lean](Internal/CoreTests.lean),
[Internal/Tests.lean](Internal/Tests.lean), and
[Tests/NamedIntegration.lean](../../Tests/NamedIntegration.lean) exercise the
typed implementation and its connection to named expressions. The existing
orthologic, FOL-translation and checker tests cover its consumers.

[Tests/NormalizationBoundary.lean](../../Tests/NormalizationBoundary.lean)
checks public signatures and executable dependencies against the ghost boundary,
allowing internal declarations only in erased proofs.
