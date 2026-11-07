# Orthologic normalization for LambdaFOL

This package computes sound equivalences and implications for the proof checker.
Its accepted comparisons are justified in `Ordered AlphaBetaEta`. Rejection does
not establish inequivalence or unprovability. There is no search fuel.

## Public interface

Import `Lisa.Orthologic`. Read these four files for the operations and their
meaning; their theorem statements use Lisa expressions and the Ordered system.

| File | What it exposes |
| --- | --- |
| **[Expression.lean](Expression.lean)** | `normalize`, `isSame`, `isImplying`: the uncached named-expression pipeline. |
| **[Equivalence.lean](Equivalence.lean)** | `ContextEq`: interchangeability in formula applications, including at function sorts. |
| **[Soundness.lean](Soundness.lean)** | Preservation, accepted-comparison soundness, failure conditions, and recognition of αβη-equivalence. |
| **[Cached.lean](Cached.lean)** | Cached entry points and exact agreement with the uncached pipeline. |

`normalize p` returns `Option Expr`. It fails exactly when `p` is ill-sorted;
otherwise its result has the same sort and is contextually equivalent to `p`.
The output's spelling is not claimed to be a unique representative of OL equivalence.

`isSame p q` returns `Option Bool`. It fails exactly when either input is
ill-sorted. Success with `true` establishes contextual equivalence at their
common sort; for formulas, it gives Ordered proofs in both directions.
Different well-sorted result sorts give `some false`.

`isImplying p q` fails unless both inputs have proposition sort. Success with
`true` gives an Ordered proof of `p ⊢ q`.

`Cached.normalize`, `Cached.isSame`, and `Cached.isImplying` have the same
results for every cache configuration. The checker uses these cached operations
through [Checker/ProofRelation.lean](../Checker/ProofRelation.lean).

## Definitions and ghost proofs

Executable definitions remain at the top level. `Internal/` contains supporting
proofs and their auxiliary constructions. Public signatures and non-erased
definitions do not depend on declarations from `Internal`; proof bodies may.
This also applies to dependencies on AlphaBetaEtaNormalization's proof files.

Termination arguments and cache certificates are erased proofs. They may use
internal lemmas without making the computation depend on ghost code. Some
proof files extend the executable declarations' namespace: declaration origins,
not namespace spelling, determine the boundary.

## The computation

1. **Canonicalize by αβη.** `AlphaBetaEtaNormalization.Algorithm.interpretNamed` checks sorts and translates
   names into typed lambda terms. `AlphaBetaEtaNormalization.Algorithm.normalize` produces their canonical
   forms. This makes αβη-equivalent inputs identical before OL starts.
2. **Expose logical structure.** `SimpleExpr.ofTerm` recognizes logical constants
   and their applications. Its internal syntax has conjunction lists, negation,
   universal quantification and individual equality. Disjunction, implication,
   biconditional and existential quantification are expressed using these.
3. **Normalize by OL.** `computeNormalForm` first normalizes children, then
   simplifies their parent. For conjunctions, it flattens and refines factors,
   removes factors implied by the others, and detects contradictions. It also
   simplifies negations, quantifiers over constants and individual equalities.
4. **Compare the results.** `isSame` uses `latticesEQ`; `isImplying` uses
   `latticesLEQ`. Conjunctions remain lists, so literal tree equality would miss
   changes in factor order. Only `normalize` reconstructs variable names.

The normalizer follows [OLEquivalenceChecker.scala](../../OLEquivalenceChecker.scala).
In particular, factor traversal order matters: `simplifyFactors` preserves its
prepend-and-prune traversal. Equality operands are oriented by a deterministic
structural order on typed terms.

Within this stage, `recognizeConst` and `recognizeApp` expose the logical
constructors; `withPolarity` applies a sign; `negate` cancels an existing
negation; and `normalizeConjunction` simplifies a conjunction or its negation.
`latticesEQ` and `latticesLEQ` retain the names of the corresponding Scala
comparisons. They return Boolean answers, while `ProvableEQ` and `ProvableLE`
state the proof guarantees described below.

During refinement, `context` is the original conjunction. `positive` records
that conjunction's outer polarity, while `sign` records the current factor's
polarity. Descending through a negation flips `sign`; it keeps the original
conjunction and its outer polarity fixed. This is why a factor may be simplified
using the other factors without being equivalent to its replacement in isolation.

## How recursion reaches formulas inside terms

`polarLEQ p s q t` asks whether the signed formula on the left implies the signed
formula on the right. A `false` sign means negation. Signs let the algorithm use
the dual conjunction rules without constructing new negated trees.
`latticesEQ` asks for both directions at proposition sort and compares children
at other sorts. The two functions call each other.

Quantifier bodies are compared by implication: a successful comparison of
`p ≤ q` permits `∀x. p ≤ ∀x. q`. Arbitrary applications instead require
**equivalence** of the function and argument. Thus comparison of
`P (εy. Q y ∨ R y)` with `P (εy. R y ∨ Q y)` reaches the lambda bodies and uses
OL there; the epsilon terms are not opaque atoms. Normalization visits those
same children before the final comparison.

`SimpleExpr s` records the expression's sort in its type. Bound indices count
enclosing binders of the same sort, following `AlphaBetaEtaNormalization.Algorithm.Term`. Translation to and
from lambda terms preserves this convention. Named output uses fresh names to
avoid capture.

## Memoization

The uncached functions are the specification. Every stored answer carries a
proof that it equals that specification's result for its key; Lean erases the
proof at runtime. Consequently, cached/uncached agreement covers negative
answers and malformed inputs as well as successful comparisons.

The cache stores named preparation, subtree normalization, recursive comparison,
and the terms used for identity checks and equality orientation. Its keys use
exact internal syntax. Erasure to lambda terms is insufficient for cache keys:
an application of `and` and a conjunction node can erase to the same term but
take different normalization paths. Hash collisions are resolved by structural
equality. Hashing and equality still traverse trees; this is not hash-consing.

The convenience functions start with an empty cache. To retain it across queries:

```lean
let (answer, cache) := (Cached.isSameMemo p q).run ({} : Cached.Cache)
let (nextAnswer, cache) := (Cached.isImplyingMemo q r).run cache
-- answer.val and nextAnswer.val have type Option Bool.
```

`Config` controls four cache categories and `Stats` records hits and misses.
Misses count computations without a cached answer, including when a category
is disabled. The `keys` category covers both lambda terms and equality-order keys.
The caller owns the cache lifetime. The checker currently shares work within
each comparison, but starts fresh for separate rule-condition tests.

## Executable support, in dependency order

These files explain how the public operations compute. They contain real data
and algorithms, not ghost implementations hidden behind public wrappers.

| File | Responsibility |
| --- | --- |
| [Syntax.lean](Syntax.lean) | Sorted OL expressions, their size, translation to typed lambda terms, and named reconstruction. |
| [StructuralOrder.lean](StructuralOrder.lean) | Deterministic orientation of individual-equality operands. |
| [Comparison.lean](Comparison.lean) | Mutually recursive lattice implication and equivalence. |
| [Normalization.lean](Normalization.lean) | Refinement, pruning, contradiction detection, and bottom-up normalization. |
| [FromLambda.lean](FromLambda.lean) | Recognize logical structure in canonical typed lambda terms. |
| **[Expression.lean](Expression.lean)** | Assemble the named-expression pipeline. |
| [CacheKey.lean](CacheKey.lean) | Exact structural comparison of cache keys. |
| [Cache.lean](Cache.lean) | Cache data, certificates, configuration, statistics, and decidable key equality. |
| [CacheAlgorithm.lean](CacheAlgorithm.lean) | Memoized traversals and recursive algorithms. |
| **[Cached.lean](Cached.lean)** | Convenient entry points and agreement theorems. |

The [proof guide](Internal/README.md) lists the supporting proof files and
explains how their results yield the contracts in `Soundness.lean`.

## Checking changes

[Tests/OrthologicBoundary.lean](../../Tests/OrthologicBoundary.lean) checks all
top-level signatures and executable definitions against the ghost boundary.

Run `lake build Lisa lisa-checker Tests` from the project root. The OL regression
files cover complementary concerns:

- [OLComparison](../../Tests/OLComparison.lean): comparison branches and derived proof steps.
- [OLNormalization](../../Tests/OLNormalization.lean): transformations, binding and Boolean-model checks.
- [OLExpression](../../Tests/OLExpression.lean): the named pipeline, malformed input and formulas inside terms.
- [OLCached](../../Tests/OLCached.lean): all cache policies, reuse, collisions and axiom checks.
- [OLCongruence](../../Tests/OLCongruence.lean): replacement in formulas and higher-order arguments.

The [reorganization plan](REORGANIZATION_PLAN.md) records the design history.
The [archived implementation](../../Archive/Orthologic/README.md) is outside the
active build.
