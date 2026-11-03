# Original quantified Weakening regression

`MGT024.trees.hex` contains the unchanged tree stream from `MGT024+1` in
`tptp400.zip`. `MGT024.proof.hex` retains its original proof through step 39,
the first rejected Weakening: `∀x (P ↔ Q)` becomes `∀x (Q → P)`.

Only the declared step count changes to 40; proof bytes after offset 824 are
omitted. All retained imports, parameters, expressions and rule bytes are
unchanged. This originally tested rejection of step 39 by the contextual
baseline and acceptance of all 40 records by the replay checker.

The export also contains the retired one-premise substitution tag 25. Since
removing that instruction, the checker rejects it at byte offset 680 with an
explicit unsupported-legacy-substitution diagnostic. The fixture bytes remain
unchanged and now test this format boundary. Quantified weakening is still
tested directly in [CheckerIntegration.lean](../CheckerIntegration.lean).

## Migrated substitution regression

`MGT024-two-premise.trees.hex` and `MGT024-two-premise.proof.hex` adapt the same
proof prefix to the two-premise rule. All 42 steps pass, including the final
quantified weakening. The final sequent, seven declared imports and all original
step conclusions are retained. The final proof has no unresolved imports.

The tree stream keeps all 736 original entries and appends four applications
for the exact pointwise comparison `E`. Original step 35 (tag 25) becomes three
steps: `E ⊢ E` by hypothesis; `∀T. body ⊢ E` by leftForall; then tag 34 using
the original premise and this comparison proof. Subsequent step references are
adjusted. No additional imports are introduced. The comparison's unreduced lambda
applications match `SubstRule.equation`; the checker verifies their equivalence
to the quantified body's instance.

Regenerate the migrated pair with `python Tests/Fixtures/migrate_mgt024.py`.
The script checks the original hashes before writing the new files. Both pairs
are covered by [SerializedCorpus.lean](../SerializedCorpus.lean), including
paged reads and file-based checking of the migrated proof.

SHA-256 of migrated decoded bytes:

- Trees: `491c0c80e77d4fe4e4c4b617e5edece1f25dd0720f6ca86d561acff423e93e43`
- Proof: `2bb0bdc9d658bb24cd9c9e4ece57e06c1707229e8c06e109daa6d31b1d1c6685`

SHA-256 of original decoded bytes:

- Original trees: `7b4da260d8b8c6ba454ac775f6c241949fd1866d96628ed12704a0358208a55d`
- Retained prefix: `3236919e66fce302499f7dc2526f8c656c24d665b5beecfa17359eb68fca1f23`
- Original full proof: `cfaf41a0c546af5a28686758e7701485a760d30d190819a594c84b595c460949`
- Source archive: `247630c0a1a55745f8cbbdf5efe92787002a1a0d1f7195954e6e3a484b85d3dc`
