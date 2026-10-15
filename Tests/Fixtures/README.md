# Original quantified Weakening regression

`MGT024.trees.hex` contains the unchanged tree stream from `MGT024+1` in
`tptp400.zip`. `MGT024.proof.hex` retains its original proof through step 39,
the first rejected Weakening: `∀x (P ↔ Q)` becomes `∀x (Q → P)`.

Only the declared step count changes to 40; proof bytes after offset 824 are
omitted. All retained imports, parameters, expressions and rule bytes are
unchanged. The contextual baseline must reject step 39; the replay checker
must accept all 40 records with no unresolved assumptions.

SHA-256 of decoded bytes:

- Original trees: `7b4da260d8b8c6ba454ac775f6c241949fd1866d96628ed12704a0358208a55d`
- Retained prefix: `3236919e66fce302499f7dc2526f8c656c24d665b5beecfa17359eb68fca1f23`
- Original full proof: `cfaf41a0c546af5a28686758e7701485a760d30d190819a594c84b595c460949`
- Source archive: `247630c0a1a55745f8cbbdf5efe92787002a1a0d1f7195954e6e3a484b85d3dc`
