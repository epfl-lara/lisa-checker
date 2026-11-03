# Orthologic normalization for LambdaFOL

This package recognizes equivalences and implications that the proof checker can
use without an explicit user proof. Every accepted comparison is justified by a
proof in `Ordered AlphaBetaEta`. A rejected comparison does not assert that the
formulas are inequivalent or that the implication is unprovable.

## Start with the public interface

Import [Expression.lean](Expression.lean) for the executable definitions, or
[ExpressionSoundness.lean](ExpressionSoundness.lean) for their guarantees.
The following functions are in `Lisa.Orthologic`:

| Function | Result |
| --- | --- |
| `normalize p` | `Option Expr`: a named expression interchangeable with `p`. |
| `isSame p q` | `Option Bool`: compare expressions of any sort for equivalence. |
| `isImplying p q` | `Option Bool`: compare formulas in the implication direction. |

`normalize` returns `none` exactly for ill-sorted input. `isSame` returns `none`
exactly when either input is ill-sorted, and `some false` for different sorts.
`isImplying` returns `none` unless both inputs are formulas. There is no fuel.

For memoized execution, import [Cached.lean](Cached.lean) or
[CachedSoundness.lean](CachedSoundness.lean) and use the same names under `Cached`.
The checker uses these cached functions through
[Checker/ProofRelation.lean](../Checker/ProofRelation.lean).

## The computation

1. **Canonicalize by αβη.** `AlphaBetaEtaNormalization.interpretNamed` checks sorts and translates
   names into typed lambda terms. `AlphaBetaEtaNormalization.normalize` produces their canonical
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
enclosing binders of the same sort, following `AlphaBetaEtaNormalization.Term`. Translation to and
from lambda terms preserves this convention. Named output uses fresh names to
avoid capture.

## What the proofs establish

The proof files build actual Ordered derivations. Three definitions connect
the internal computation to those derivations:

- `ContextEq s p q` says that every well-sorted expression `k : s → prop`
  gives proofs of both `k p ⊢ k q` and `k q ⊢ k p`. This expresses replacement
  even at function sorts, without adding a higher-order equality symbol.
- `ProvableEQ p q` requires this contextual equivalence after reconstructing
  names under every naming assignment.
- `ProvableLE p q` requires a proof of `p ⊢ q` under every naming assignment.

Application and lambda congruence are derived using the proof system's
substitution rule. Freshness conditions ensure that these derivations also
work underneath binders.

The main results are `latticesEQ_sound`, `polarLEQ_sound` and
`computeNormalForm_sound`. They establish accepted equivalence, accepted
implication and preservation by normalization, respectively.
`isSame_sound` and `isImplying_sound` carry those results back to the original
named inputs. `prepare_alphaBetaEta` proves that well-sorted αβη-equivalent
inputs have identical prepared expressions.

These are soundness results, not completeness or uniqueness-of-normal-form
results. The tests audit their dependencies against Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

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

## Files in dependency order

All package Lean files appear below, with their local dependencies first.
**Bold files** contain the main algorithms and end-to-end guarantees; the others
provide their representation, proof lemmas or cache support.

| File | What to read it for |
| --- | --- |
| [Syntax.lean](Syntax.lean) | Typed internal expressions, binding, translation to lambda terms and named reconstruction. |
| **[Comparison.lean](Comparison.lean)** | The mutual recursion of implication and equivalence. |
| [StructuralOrder.lean](StructuralOrder.lean) | Deterministic operand order for individual equality. |
| **[Normalization.lean](Normalization.lean)** | The OL transformations and their traversal order. |
| [Derivation.lean](Derivation.lean) | Reusable Ordered proof steps for connectives, substitution and quantifiers. |
| [Congruence.lean](Congruence.lean) | Contextual equivalence and replacement beneath applications and lambdas. |
| [Provability.lean](Provability.lean) | Transfer those proof steps to internal expressions and conjunction lists. |
| **[ComparisonSoundness.lean](ComparisonSoundness.lean)** | Justify each comparison branch by an Ordered derivation. |
| **[NormalizationSoundness.lean](NormalizationSoundness.lean)** | Justify each transformation, then the whole normalizer. |
| [FromLambda.lean](FromLambda.lean) | Recognize logical structure in typed lambda terms. |
| [FromLambdaSoundness.lean](FromLambdaSoundness.lean) | Prove the recognized forms equivalent to the input terms. |
| **[Expression.lean](Expression.lean)** | The complete executable pipeline on Lisa expressions. |
| **[ExpressionSoundness.lean](ExpressionSoundness.lean)** | Public soundness, αβη invariance, sorting and failure conditions. |
| [CacheKey.lean](CacheKey.lean) | Exact equality for keys and its correctness proof. |
| **[Cached.lean](Cached.lean)** | Memoized computation with exact-agreement certificates. |
| [CachedSoundness.lean](CachedSoundness.lean) | Transfer soundness to the cached public functions. |

## Checking changes

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
