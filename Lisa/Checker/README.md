# Executable proof checker

The checker reads a sequence of proposed inference steps and returns either an
error or a certified conclusion with its unresolved assumptions. It uses the
verified [Orthologic comparison](../Orthologic/README.md), which canonicalizes
expressions by αβη before OL normalization and comparison.

## Start here

| Main file | What to read |
| --- | --- |
| **[ProofRelation.lean](ProofRelation.lean)** | The relation used in certificates: Ordered αβη implication for formulas, contextual equivalence at other sorts. |
| **[Data.lean](Data.lean)** | `Statement`, `Checked`, `ClosedChecked`, and the possible errors. |
| **[ProofData.lean](ProofData.lean)** | The rule requests, signed premise references, and array of proof steps accepted as input. |
| **[Check.lean](Check.lean)** | `check` checks all steps; `checkClosed` additionally requires the requested conclusion and no unresolved assumptions. |
| **[Soundness.lean](Soundness.lean)** | The guarantees for successful checks, including the final PureFol theorem. |

`Statement` stores two lists of expressions. Its `sequent` views them as finite
sets for the proof calculus. `Checked` retains the actual conclusion and its
assumptions, together with an erased certificate of an Imported derivation.
`ClosedChecked relation target` certifies the specified target with no assumptions.

Premise references `0, 1, …` refer to earlier local steps; `-1, -2, …` refer to
declared external imports. An import is an assumption until it is discharged or
supplied with a proof when using the soundness theorem.

## What the guarantees say

| Theorem | Guarantee |
| --- | --- |
| `Checked.sound` | Supplying Ordered αβη proofs of all recorded assumptions gives an Ordered αβη proof of the checked conclusion. |
| `ClosedChecked.sound` | A closed result gives an Ordered αβη proof without additional assumptions. |
| `ClosedChecked.sound_pureFol` | If its conclusion is well-sorted and first-order-compatible, a closed result gives a PureFol proof of its canonical translation. |

PureFol includes epsilon. The last theorem restricts only the conclusion, not
intermediate formulas. Its restrictions and translation are defined publicly in
LambdaFol's [FirstOrder.lean](../LambdaFol/FirstOrder.lean) and
[Translation.lean](../LambdaFol/Translation.lean).

OL supplies **positive evidence** for `ProofRelation`. Failure means the
algorithm did not establish a condition; it does not establish its negation.
Acceptance is not assumed to be transitive or complete. During discharge, an
assumption remains recorded whenever the executable equivalence test fails.

## Follow the execution

| Supporting file | Role |
| --- | --- |
| [Encoding.lean](Encoding.lean) | Compute a sequent formula directly from the input lists. |
| [Interfaces.lean](Interfaces.lean) | `Test P` combines a Boolean with an erased proof that success implies `P`; `Testable` supplies tests for rule conditions. |
| [StatementTests.lean](StatementTests.lean) | Test whole-sequent implication, equivalence, and equivalence to truth. |
| [Algorithm.lean](Algorithm.lean) | Resolve references and check each rule's conditions, collecting unresolved assumptions. |
| [Display.lean](Display.lean) | Render expressions and diagnostics. |
| [Binary.lean](Binary.lean) | Decode paged binary streams and check their steps with the same algorithm. |

The algorithm uses `Orthologic.Cached`. Each expression comparison shares a
verified cache across its recursive calls; the checker does not retain that
cache across separate condition tests or proof steps. There is no search-depth
budget.

## Proofs and the ghost boundary

[Internal/](Internal/README.md) contains the relation properties, the
list/finite-set correspondence, rule-certificate lemmas, and the derivation of
soundness through Imported, Weakened, Ordered, and PureFol.

Internal declarations occur only in erased proofs in the public layer. Public
definitions and theorem statements use public declarations, including those of
other packages. Executable supporting operations remain outside `Internal`.
Small certificate proofs stay beside their rule checks; larger shared arguments
are in the proof folder. The boundary concerns declaration dependencies, not
whether a file imports a proof module to use its theorems.

## Run and verify

```text
lake build Lisa lisa-checker Tests
lake exe lisa-checker [--limit N] [--closed] [--trace] PREFIX|DIRECTORY ...
```

[CheckerBoundary.lean](../../Tests/CheckerBoundary.lean) checks public types and
non-erased definition bodies for dependencies on ghost declarations.
[Checker.lean](../../Tests/Checker.lean),
[CheckerIntegration.lean](../../Tests/CheckerIntegration.lean), and
[SubstitutionChecker.lean](../../Tests/SubstitutionChecker.lean) exercise checking
and its guarantees. [Binary.lean](../../Tests/Binary.lean),
[SubstitutionBinary.lean](../../Tests/SubstitutionBinary.lean), and
[SerializedCorpus.lean](../../Tests/SerializedCorpus.lean) cover decoding and
serialized inputs.

A bundle contains proofs relative to explicit imports; theorem names do not
automatically resolve dependencies. The [binary format](BINARY_FORMAT.md)
specifies supported payloads and exporter requirements. Two-premise substitution
uses tags **33 and 34**. Retired one-premise tags **24 and 25** produce an error.
