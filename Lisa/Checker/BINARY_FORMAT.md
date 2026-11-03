# Two-premise substitution in binary proofs

The checker reads the existing paired `.trees` and `.proof` streams. The shared
tree table and bundle headers keep their existing layout. Two additional step
tags encode the simultaneous substitution rules:

| Tag (decimal) | Rule |
| --- | --- |
| 33 | `leftSubst` |
| 34 | `rightSubst` |

Tags 24 and 25 retain their old meaning and are rejected explicitly; they are
never interpreted as the new rules. Tags 11, 21, 27–29 and 32 remain unsupported.
These additions belong to this checker's format. An external exporter must emit
the new payload and comparison premise to use them.

## Layout

All numbers are big-endian. `count16` is a nonnegative signed 16-bit count
(0–32767). `treeRef` is a nonnegative signed 32-bit index into the `.trees`
table. `proofRef` is a signed 32-bit integer: nonnegative values refer to earlier
steps, while `-1`, `-2`, etc. refer to imports 0, 1, etc.

Both new step tags have this layout, in the order shown:

```text
u8       tag                         33 or 34
count16  antecedentCount
treeRef  antecedents[antecedentCount]
count16  succedentCount
treeRef  succedents[succedentCount]

proofRef premise                     sequent being transformed
proofRef comparison                  sequent proving the comparisons
count16  replacementCount
repeat replacementCount times:
    treeRef  source
    treeRef  target
    count16  argumentCount
    treeRef  arguments[argumentCount]    each must refer to a variable
count16  parameterCount
treeRef  parameters[parameterCount]      each must refer to a variable
treeRef  body                           formula context
```

`parameters[i]` is the context hole replaced by the source or target of pair
`i`. Preserve list order, including duplicate context parameters: substitution
is simultaneous and the last replacement wins for repeated parameters.
The number and sorts of context parameters must match the replacement list.

`arguments` contains the independent variables used to compare a particular
pair pointwise. Their sorts may themselves be proposition or function sorts.
The source and target must have the same sort, and applying them to these
arguments must consume all arrow domains and produce an individual or formula.
Ground pairs use an empty argument list.

## Comparison premise

For each pair, apply its source and target to its argument variables. Compare
the results with `=` for individuals or `↔` for formulas. The comparison
formula `E` is their left-associated conjunction; an empty list gives `⊤`, and
a singleton gives its comparison directly.

The second premise must have `E` in its succedent. This occurrence is checked
by **syntactic equality**, so exporters should construct it exactly as
`SubstRule.equation` does, retaining applications of lambdas if present.
If a proof establishes an αβη- or OL-equivalent expression instead, add a
restate step with `E` as the declared conclusion before referring to it.

Within each argument list, the variables must be distinct and absent from the
free variables of both compared expressions. They must also be absent from
the comparison premise's antecedents and its other succedent formulas. They
may occur in the first premise and the final conclusion.

The decoder checks counts, expression references and variable constructors.
The ordinary checker then checks both proof references, sorts, arity,
freshness, the comparison formula and the declared conclusion. Binary input
does not bypass any of the in-memory rule checks. Both premises contribute
their unresolved imports to the result.

## Examples and validation

- [Tests/Binary.lean](../../Tests/Binary.lean) has independently constructed
  payloads for both tags, exact field checks, truncations and malformed fields.
- [Tests/SubstitutionChecker.lean](../../Tests/SubstitutionChecker.lean) runs
  its positive and negative rule cases through both the in-memory checker and
  the two binary streams, with page sizes 1, 7 and 65536. The small test-only
  writer is [SubstitutionBinary.lean](../../Tests/SubstitutionBinary.lean).
- [MGT024-two-premise.proof.hex](../../Tests/Fixtures/MGT024-two-premise.proof.hex)
  is a migrated Scala regression, checked together with its `.trees.hex` file
  by [SerializedCorpus.lean](../../Tests/SerializedCorpus.lean). The original
  fixture still tests rejection of retired tag 25.

There is no automatic translation of legacy substitution inside the reader.
For this fixture, [migrate_mgt024.py](../../Tests/Fixtures/migrate_mgt024.py)
reproducibly adds the comparison proof and adjusts the subsequent references.
