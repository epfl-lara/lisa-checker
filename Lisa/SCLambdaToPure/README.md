# From Ordered to first-order logic

Read the three public files in this order:

| File | What it presents |
| --- | --- |
| [Pure.lean](Pure.lean) | The independent first-order syntax and sequent calculus, including epsilon. |
| [A.lean](A.lean) | A's formula classes, contexts, and inference rules, without schematic instantiation. |
| [Statements.lean](Statements.lean) | `a_iff_pure`, `ordered_iff_a`, and `ordered_iff_pure`, connecting the actual Ordered system to A and Pure. |

The proof still follows the paper's stages:

```text
Ordered AlphaBetaEta → B → A → Pure
```

B remains a separate calculus: its formulas are considered modulo αβη,
it permits schematic instantiation, and it has no primitive whole-sequent
restatement rule. A has the same logical rules without schematic instantiation.
Both retain the project's generalized simultaneous replacement and epsilon rules.

There is no additional system C. The old `C.lean` has been split between the
public equivalence statements and the supporting constructions. Its final result
is now available as `Lisa.SCLambdaToPure.ordered_iff_pure`.

## The concluding theorem

For sorted contexts `Γ` and `Δ` satisfying `FirstOrderBoundary`:

```lean
OrderedReduction.Provable Γ Δ ↔
  Pure.Provable
    (Readback.canonicalContext Γ)
    (Readback.canonicalContext Δ)
```

`OrderedReduction.Provable` means provability in `Ordered AlphaBetaEta`.
Only the concluding formulas must satisfy the boundary: intermediate proof
formulas may contain higher-order variables and lambda expressions.
The boundary permits first-order function and predicate constants, logical
constants including epsilon, and free individual and proposition variables.
Free propositions become nullary predicates in Pure.

`Pure` here is first-order logic **with epsilon**, including its extensionality
rule. This package does not eliminate epsilon or invoke model-theoretic
completeness. Assumptions remain in the antecedent throughout.

## A to Pure

The [AToPure](AToPure) directory justifies the paper's step of replacing formulas
throughout an A proof by their canonical first-order forms.

Start with [Equivalence.lean](AToPure/Equivalence.lean), then
[Derivation.lean](AToPure/Derivation.lean), the induction on A proofs.
[The A-to-Pure reading guide](AToPure/README.md) connects each supporting file
to a step of the paper's argument and explains why replacement under binders
needs a separate compatibility proof.

The forward proof's files are grouped by responsibility: normalization and
first-order shape; reading into Pure syntax; replacement and binding; and the
proof translation. The converse is under [AToPure/Reverse](AToPure/Reverse).
It retains the existing route Pure → Ordered → B → A.

A's formula classes and proof system are defined directly in [A.lean](A.lean).
[FormulaClasses.lean](AToPure/FormulaClasses.lean) contains their properties and
derived individual substitution rules. [Boundary.lean](AToPure/Boundary.lean)
defines the conclusion restriction and canonical first-order translation.
[Statements.lean](Statements.lean) presents the final theorems using the proofs
in the submodules. Supporting proofs import definitions, never `Statements`.

## Ordered to A

The [OrderedToA](OrderedToA) directory contains B and the elimination of
schematic instantiation:

| File | Role |
| --- | --- |
| [B.lean](OrderedToA/B.lean) | Defines B and proves `B.toA` using admissibility of instantiation in A. |
| [ToB.lean](OrderedToA/ToB.lean) | Translates actual Ordered derivations into B. |
| [SequentEncoding.lean](OrderedToA/SequentEncoding.lean) | Derives Ordered's whole-sequent restatement using B's logical rules. |
| [InstantiateProof.lean](OrderedToA/InstantiateProof.lean) | Pushes a schematic substitution through an A proof, freshening variables when necessary. |
| [InstantiateReplacement.lean](OrderedToA/InstantiateReplacement.lean) | Handles generalized simultaneous replacement in that proof. |
| [ToPure.lean](OrderedToA/ToPure.lean) | Composes Ordered → B → A → Pure for the final theorem. |
| `Substitution*`, `Conjunction` | Supporting syntax, freshness, and conjunction lemmas. |

The folders group responsibilities, not completely independent libraries.
The A-to-Pure argument uses some named-substitution lemmas from `OrderedToA`.
Conversely, both parts use A's formula classes. In addition, the existing reverse
proof of A–Pure equivalence takes the route Pure → Ordered → B → A. The split
preserves this proof rather than adding a second reverse translation.

## Validation

```sh
lake build Lisa lisa-checker Tests
```

`Tests.SCLambdaToPure` and `Tests.PureEpsilon` exercise both directions, nested
binders and epsilon, freshness collisions, simultaneous substitution, and
higher-order intermediate formulas. They audit the final proof's dependencies
on the B → A → Pure stages and reject axioms beyond `propext`, `Classical.choice`,
and `Quot.sound`.

[CLEANUP_PLAN.md](CLEANUP_PLAN.md) is a historical review of the earlier flat
layout, not the current file inventory.
