# Lisa checker continuation handoff

Snapshot date: **2026-10-25**. Read this before the long transcript. This is a summary
of the current state and decisions, not a substitute for the Lean theorem statements.

## Current task and exact stopping point

The user is developing a verified Lean implementation of Lisa's lambda-FOL proof
checker and now wants to connect it to independent pure first-order logic, following
`lamfol.tex`. Their last implementation request before this export was:

> Alright! Please start with A and its translation to pure

An initial stage was implemented and compiled. **The concrete A-to-Pure conservativity
theorem is not finished.** In particular, do not mistake the abstract
`A.Interpretation` interface and its conditional proof-transport theorem for a
completed construction of that interpretation.

The latest saved full build succeeded with **1703 jobs**:

```text
lake build Lisa lisa-checker Tests
```

See `verification/last-build.log`. The source has not been changed by this export.
This is a record of the source-machine build, not a claim that a build has already
run on the destination machine. The recent implementation reported no production
`sorry` or new axioms. Axiom inspection of the new theorems reported only the usual
Lean logical axioms (`propext`, `Classical.choice`, `Quot.sound`, as applicable).

## Files for the current A-to-Pure work

Paths below are relative to `project/`.

| File | Current role |
| --- | --- |
| `Lisa/SCLambdaToPure/Pure.lean` | Independent pure FOL sequent calculus using mathlib's FOL syntax, fixed sentence-theory axioms, and free individual variables numbered by `Nat`. |
| `Lisa/SCLambdaToPure/A.lean` | System A on intrinsically sorted subtypes of alpha-beta-eta equivalence classes. Ordinary classical sequent rules, individual-variable equality substitution, no instantiation or epsilon rule. Conversion is equality of classes rather than an explicit inference rule. |
| `Lisa/SCLambdaToPure/Canonical.lean` | Neutral and beta-normal eta-long predicates on existing typed Lambda terms, plus `normalize_canonical`. |
| `Lisa/SCLambdaToPure/FirstOrderShape.lean` | First-order shape predicates and the canonical-form theorem for the restricted signature and ground free variables. The namespace is `FirstOrderShape`, not `FirstOrder`, to avoid shadowing mathlib. |
| `Lisa/SCLambdaToPure/Readback.lean` | Executable partial readback into a concrete mathlib language, alpha-beta-eta invariance, and several connective laws. |
| `Lisa/SCLambdaToPure/AToPure.lean` | Every A rule is transported to Pure **assuming** an `Interpretation` satisfying stated laws and a translation of theory axioms. No concrete instance satisfying all laws is provided yet. |
| `Lisa/SCLambdaToPure.lean` | Aggregate import with an explicit description of the unfinished conservativity result. |
| `Tests/SCLambdaToPure.lean` | Regression tests, registered in `lakefile.toml`. |

### Important representation details

- `A.Expression s` is a subtype of `AlphaBetaEta.Term` recording its sort. A's
  formulas have sort `prop`, individual terms have sort `ind`.
- `A.Fresh` uses the existence of a representative without the variable. This is
  intentional: beta expansion can introduce a syntactically free but unused name.
- The current A calculus accepts arbitrary sorted representatives/constants.
  The paper's signature and free-variable restrictions are separate hypotheses
  of the canonical-form results; do not silently assume them for every A formula.
- `FirstOrderShape.canonical_lamfol` establishes the canonical/formula-shape result
  for a successfully interpreted named formula with permitted constants and free
  variables of sort `ind` or `prop`. The intermediate proof may still have other
  free symbols; those need a proof-preserving elimination argument.
- Readback uses a universal FOL symbol type with a flag distinguishing schematic
  symbols from constants. It recognizes logical constants by full identifier and
  sort, not merely by display name.
- Free identifier encoding into `Nat` is proved injective. Free proposition
  variables become nullary schematic predicates.
- Lisa Lambda bound indices are counted per sort and nearest binder first.
  Mathlib's bounded formulas use levels: readback assigns a new binder `Fin.last`
  and keeps earlier binders via `Fin.castSucc`. Nested/shadowed quantifier tests
  check this convention.
- Readback rejects malformed applications, dangling bound variables, epsilon, and
  genuine higher-order applications. It does not hide them as arbitrary FOL atoms.
- The concrete reader is partial; the `Interpretation` interface requires a total
  map. Establish a suitable restricted domain/grounding construction before trying
  to populate that interface. If a cleaner statement is needed, change it honestly
  rather than adding assumptions that amount to the desired theorem.

### Work remaining next

1. Fix the precise signature and endpoint restrictions for the theorem. Preserve
   the distinction between a fixed theory of pure sentences and freely instantiable
   schemas. Reserved logical names also need care in any unrestricted inverse embedding.
2. Eliminate higher-order schematic symbols occurring only in intermediate A
   sequents by a uniform, capture-avoiding replacement. The endpoint must be
   preserved. Verify the induction for every rule and its freshness conditions.
3. Prove the concrete bridge laws still missing: equality, capture-avoiding
   substitution, quantifiers, eigenvariable freshness, and total readback on the
   applicable normalized fragment. Connect those facts to the conditional transport.
4. Canonicalize **every intermediate formula**, not just the concluding sequent,
   and prove the concrete A-to-Pure result. Establish the reverse embedding as
   required by the paper's equivalence claim.
5. Only then move to B (instantiation elimination), and later epsilon elimination
   and the connection to the actual `Ordered AlphaBetaEta` calculus.

The current generalized simultaneous substitution rule in the actual checker is
stronger than A's individual-variable substitution. Its conservativity needs an
explicit argument in the later connection; the paper's old rule should not be
silently substituted for the implemented one.

Tests already cover beta/alpha quotient identity, freshness through an unused beta
argument, a higher-order-lambda canonicalization example, alpha-beta-eta invariant
readback, rejection cases, identifier injectivity, first-order function applications,
nested quantifier levels, shadowing, and concrete connective readback laws.

## Architecture and accepted design choices

### Lambda and expression equality

- The newer Lambda implementation replaced the older one. The active code is
  `Lisa/Lambda/`; do not revive `LambdaV2` as a parallel implementation.
- Typed syntax uses `Term s` without a context `Gamma`, with per-sort bound-variable
  indices. `Lisa.Expr` remains the named syntax used around the checker.
- Normalization by evaluation has no fuel limit. Arrow values are ordinary
  functions; ground semantic values retain the depth bookkeeping needed at readback.
- Use the explicit `AlphaBetaEta` naming. Old files called `Conversion` were renamed.

### Proof systems and relation interfaces

- `Standard` was removed. The baseline is `Ordered AlphaBetaEta`; `Ordered` and
  `Weakened` are the intended main proof systems.
- Do not reintroduce `OrderAlgebra` or `LogicalOrder` assumptions into the main
  proof-system interfaces. A diagonal/alpha-beta-eta relation is valid there; a
  supplied relation need not itself satisfy all lattice laws.
- `ExprRel`, preorder assumptions, and the limited relation congruence assumptions
  are separate. The required congruence interface covers equality and implication.
- Ordered has ordinary structural weakening and explicit truth/falsehood rules.
  The order-based rule is `restateWeaken`; a redundant separate restate rule was removed.
- `OrderedComparison` relates different instantiations by admissibility on
  two-formula sequents: a source comparison of `a` and `b` yields a target proof
  of `{a} |- {b}` (with the appropriate formula hypotheses).
- `OrderedEncoding` supplies the proof steps needed to move between sequents and
  their formula encoding. Correspondence proofs use proof rules, not global
  logical-order assumptions.
- Executable checker code is under `Lisa/Checker/`; `Imported` and
  `ImportedWeakened` remain outside it as proof-system definitions/translations.

### Orthologic implementation

The intended pipeline follows `OLEquivalenceChecker.scala`:

1. Canonicalize by alpha-beta-eta.
2. Normalize by the extended OL algorithm, descending monotonically through
   quantifiers and by equivalence through the other expression constructors.
3. Compare normalized results using the lattice equality procedure, accounting
   for commutativity rather than requiring literal ordered-tree equality.

The active implementation proves soundness in `Ordered AlphaBetaEta`. Completeness
with respect to arbitrary ortholattices is not a goal of this redesign.

Main groups: `Syntax`, `Lowering`, `Comparison`, `Normalization`, their soundness
files, `Congruence`, `Derivation`, `Provability`, `StructuralOrder`, `Expression`,
`ExpressionSoundness`, `CacheKey`, `Cached`, and `CachedSoundness`.

Memoization with structural keys is verified against the uncached implementation.
The cache is currently per query. The user explicitly deferred reference-identity /
hash-consing optimizations because their complexity was not worthwhile yet.

The old Combined/Quantified implementation and related OL code live in
`Archive/Orthologic/`, outside the active build. **Keep that archive.** The old
combined/quantified split and generic matching machinery should not be revived.

### Generalized substitution and binary format

- Active substitution is simultaneous and has two premises. The comparison premise
  proves a conjunction of pointwise comparisons for all replacements.
- Replacements can have arbitrary simple sorts. Their argument lists exhaust the
  arrow domains; the final comparison is individual equality or propositional iff.
- The comparison argument variables must be fresh in the residual contexts of the
  comparison premise. They need not be fresh in the unrelated residual contexts of
  the first premise. Consult the actual rule and `Lisa/SUBSTITUTION_RULE_PLAN.md`;
  early conversation answers about freshness were corrected.
- No new higher-order equality sort was introduced.
- The old substitution checker cases were removed, not retained as alternate
  primitives. Old binary tags 24/25 are deliberately rejected.
- Binary tags 33/34 implement left/right substitution. See
  `Lisa/Checker/BINARY_FORMAT.md`. The decoder checks structural validity and the
  checker checks the proof-rule conditions.
- `Tests/SubstitutionBinary.lean` provides a test-only writer, not a production
  exporter. `Tests/SubstitutionChecker.lean` covers memory and binary checking.
- The migrated `MGT024-two-premise` fixture preserves the original conclusion:
  42 steps, 7 imports, no unresolved assumptions in the recorded CLI check.
  `Tests/Fixtures/migrate_mgt024.py` reproduces that specific migration. The old
  fixture remains a regression test for rejecting the obsolete format.
- A general Scala producer migration/exporter has not been implemented.

## Working style and scope constraints

- The user wants strict simplification, understandable definitions, and short,
  concrete explanations. Do not call an abstraction a finished proof.
- Read the actual code before claims; distinguish proved facts from plans or
  inferences. Some earlier review findings and terminology were explicitly rejected.
- Preserve user changes and old code retained for reference. Breaking changes can
  be appropriate when authorized, but report substantial mathematical complications.
- Do not revisit the discarded definite-description topic; this formalization uses epsilon.
- Do not add placeholders, axioms, unrequested generalization, or extra layers to
  conceal a missing argument. Follow dependencies and keep touched files compiling.
- The original working tree has substantial uncommitted changes. The exported Git
  checkout deliberately retains those as changes rather than making a synthetic commit.

## Useful starting points

- `lamfol.tex`: mathematical argument and intended chain.
- `Lisa/SCLambdaToPure.lean` and `Lisa/SCLambdaToPure/`: current continuation point.
- `Lisa/WALKTHROUGH.md`: project guide.
- `Lisa/Lambda/README.md`: Lambda package explanation.
- `Lisa/Checker/README.md` and `BINARY_FORMAT.md`: checker and serialization.
- `Lisa/Orthologic/REORGANIZATION_PLAN.md`: implemented OL redesign/status.
- `Lisa/SUBSTITUTION_RULE_PLAN.md`: rule-change rationale and side conditions.
- `COMMENTS.md`: user review notes; some refer to old names or superseded designs.
- `../conversation/CONVERSATION.md`: chronological discussion and corrections.

Read historical plans against the current implementation; they are not necessarily
current API specifications.
