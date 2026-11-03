# Previous orthologic implementation

This directory preserves the implementation replaced by milestone 5 of the
[reorganization plan](../../Lisa/Orthologic/REORGANIZATION_PLAN.md). Sources were
copied before the checker migration; retired files were checked byte-for-byte
against these copies before removal from the active module tree.

It contains:

- The old `Lisa/Orthologic` algebra, normalizer, completeness proofs and caches.
- `Lisa/Combined`, `Combined.lean`, and `CombinedCached.lean`, including the
  Combined, Quantified and Replay comparisons.
- The old checker interfaces, matching/fallback implementation, binary reader
  and CLI, plus the Lambda adapters they used.
- A snapshot of the tests and Lake configuration before migration. The common
  serialized fixtures remain in the active `Tests/Fixtures` directory.

This is a source reference, excluded from the active Lake targets. Original
module names and imports are preserved so comparisons remain readable; importing
these files directly into the new tree is not supported. To experiment with the
old implementation, restore the relevant original paths in a separate checkout,
including its checker interfaces and build configuration.

The maintained implementation lives in [Lisa/Orthologic](../../Lisa/Orthologic)
and [Lisa/Checker](../../Lisa/Checker). Core syntax, proof-system, rule-checking,
binary and corpus tests remain active. Tests specific to the retired backends
live here; the migrated active tests exercise the new checker instead.
