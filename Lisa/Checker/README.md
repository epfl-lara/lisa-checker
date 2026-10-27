# Executable proof checker

The checker uses one expression comparison pipeline:

1. Elaborate and canonicalize by αβη using `Lambda`.
2. Normalize by extended orthologic, recursively including formulas inside
   terms and higher-order arguments.
3. Compare normal forms with `latticesEQ` for equivalence or `latticesLEQ`
   for implication. The latter includes quantifier monotonicity.

`Orthologic.Cached` implements the pipeline with verified memoization. Each
expression comparison starts a cache, shared throughout its recursive work.
The checker does not yet retain a cache across separate rule-condition tests or
proof steps. The public `Orthologic.Cached.*Memo` operations also support caller-managed
cache reuse. There is no search-depth budget.

## Reading order

| File | Purpose |
| --- | --- |
| [ProofRelation.lean](ProofRelation.lean) | Define the logical relation used in certificates, in terms of actual `Ordered AlphaBetaEta` proofs. Derive its preorder and congruence properties. |
| [Encoding.lean](Encoding.lean) | Prove that the input lists and abstract finite sets encode provably equivalent sequents, including permutation and duplicates. |
| [Interfaces.lean](Interfaces.lean) | `Test P` contains a Boolean and a proof that success establishes `P`. `Testable` supplies such tests for compound rule conditions. |
| [Data.lean](Data.lean) | Statements, positive whole-sequent tests, checked certificates and errors. |
| [Check.lean](Check.lean) | Check references and rules, track unresolved imports, and build erased Imported derivations. |
| [Soundness.lean](Soundness.lean) | Convert a successful result into an actual `Ordered AlphaBetaEta` proof when the recorded assumptions are supplied. Closed results need no assumptions. |
| [Display.lean](Display.lean) | Render expressions and diagnostics. |
| [Binary.lean](Binary.lean) | Decode paged binary streams and invoke the same checker. |

## What success and failure mean

At formula sort, `ProofRelation p q` requires a proof of `p ⊢ q` in
`Ordered AlphaBetaEta`. At other sorts it requires contextual equivalence:
the expressions can replace each other inside formulas. It also preserves
sorts. This is the relation used by the existing generic proof systems, not a
new proof system or an executable decision procedure for provability.

The OL algorithm supplies positive evidence for this relation. A failed test
only means that the algorithm did not establish the condition. Consequently,
there is no `DecidableRel ProofRelation` instance, and algorithmic acceptance
is not assumed to be transitive or complete.

`Checked.sound` resolves the recorded assumptions and yields an Ordered αβη
derivation. `ClosedChecked.sound` provides the same guarantee for a closed
certificate. The bridge uses the existing Imported–Weakened and
Weakened–Ordered translations, followed by `Ordered.translate`.

Discharge removes an assumption only when the executable comparison succeeds.
Any unrecognized assumption remains recorded, even if its equivalence happens
to be provable in the reference relation. This distinction is necessary for an
incomplete comparison algorithm.

## Running it

```text
lake build Lisa lisa-checker Tests
lake exe lisa-checker [--limit N] [--closed] [--trace] PREFIX|DIRECTORY ...
```

The CLI uses the memoized pipeline automatically. The old `--budget` and
`--ol-cache` backend options have been removed. A bundle contains proofs relative
to its explicit imports; theorem names do not automatically resolve dependencies.
Two-premise substitution uses tags **33 and 34**; see
[the binary format](BINARY_FORMAT.md) for the payload and exporter requirements.
Other supported layouts are unchanged. Retired one-premise substitution tags
24 and 25 still produce an explicit error.

The previous implementation is preserved in
[Archive/Orthologic](../../Archive/Orthologic/README.md), outside active builds.
