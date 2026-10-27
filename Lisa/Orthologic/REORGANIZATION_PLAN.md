# Reorganizing the OL checker around the Scala implementation

## Current implementation status

**Milestones 1–5 are implemented.** The internal comparison, normalizer, and
named-expression interface are executable, terminate without fuel, and have full soundness proofs in
`Ordered.ProofTree AlphaBetaEta`. The substitution-rule obstacle recorded below
has been resolved by the agreed two-premise rule.

| File | Role |
| --- | --- |
| [Syntax.lean](Syntax.lean) | Intrinsically sorted internal expressions, n-ary conjunctions, quantifiers, equality, applications and lambdas; erasure and reification through the Lambda package. |
| [Comparison.lean](Comparison.lean) | Mutually recursive `latticesEQ` and `polarLEQ`, with `latticesLEQ` as the positive-polarity entry point. |
| [Derivation.lean](Derivation.lean) | Ordinary Ordered proof steps: propositional reasoning, quantifiers, equality symmetry, and contextual substitution. |
| [Congruence.lean](Congruence.lean) | `ContextEq`: equivalence at any sort, expressed by interchangeability in formula contexts. Application and lambda congruence are derived from the proof rules. |
| [Provability.lean](Provability.lean) | Define `ProvableLE` and `ProvableEQ`; prove constructor and n-ary lattice lemmas, including reconstruction with a common fresh binder name. |
| [ComparisonSoundness.lean](ComparisonSoundness.lean) | The complete comparison soundness theorem, including the mutual calls at arbitrary sorts. |
| [Normalization.lean](Normalization.lean) | Contextual refinement, factor pruning, contradiction detection, equality orientation, quantifier simplification, and `computeNormalForm`. |
| [StructuralOrder.lean](StructuralOrder.lean) | Short-circuiting structural comparison for equality orientation, retaining sorts without allocating printed strings. |
| [NormalizationSoundness.lean](NormalizationSoundness.lean) | Correctness of every local transformation and of the complete bottom-up normalizer. |
| [Lowering.lean](Lowering.lean) | Translate canonical typed Lambda terms into internal OL expressions, recognizing logical constants by identifier and sort. |
| [LoweringSoundness.lean](LoweringSoundness.lean) | Derive the connective expansions and existential duality in Ordered; prove translation preserves contextual equivalence, including beneath binders. |
| [Expression.lean](Expression.lean) | Public `normalize`, `isSame`, and `isImplying` functions: elaborate once, canonicalize by αβη, then normalize and compare by OL. |
| [ExpressionSoundness.lean](ExpressionSoundness.lean) | Soundness for the original named inputs, αβη invariance and acceptance, sort preservation, and exact failure conditions. |
| [CacheKey.lean](CacheKey.lean) | Exact structural equality for sorted cache keys, proved correct independently of erasure and hashing. |
| [Cached.lean](Cached.lean) | Shared caches for named preparation, recursive normalization, recursive comparison, and structural keys; every result carries an exact-agreement certificate. |
| [CachedSoundness.lean](CachedSoundness.lean) | Transfer the public soundness theorems to the cached entry points. |
| [Tests/OLComparison.lean](../../Tests/OLComparison.lean) | Comparison regressions, constructor derivations and finite Boolean-model checks. |
| [Tests/OLNormalization.lean](../../Tests/OLNormalization.lean) | Normalization regressions, higher-order and mixed-sort binding cases, finite Boolean-model checks, and axiom audits. |
| [Tests/OLExpression.lean](../../Tests/OLExpression.lean) | End-to-end named-input regressions, all connective translations, malformed inputs, capture avoidance, Boolean-model checks, and public-theorem axiom audits. |
| [Tests/OLCached.lean](../../Tests/OLCached.lean) | Cache-policy agreement, positive/negative reuse, recursive sharing, structural key distinctions, forced hash collisions, and axiom audits. |

### What has been proved

`ProvableLE p q` means that, for every naming assignment used to reconstruct
expressions, there is an actual Ordered proof of `p ⊢ q`. `ProvableEQ p q` means
that the reconstructed expressions can replace each other in every well-sorted
formula context. The latter applies to individual, proposition and function
sorts alike; it is a definition in terms of Ordered proofs, not an extra axiom.

The principal theorems are:

```lean
polarLEQ_sound       -- a successful polarized comparison gives ProvableLE
latticesEQ_sound     -- a successful equivalence comparison gives ProvableEQ
computeNormalForm_sound (p : SimpleExpr s) :
  ProvableEQ (computeNormalForm p) p
normalizedLEQ_sound  -- comparison after normalization implies original provability
normalizedEQ_sound   -- equivalence after normalization implies original equivalence
prepare_sound        -- the named input and its internal normal form are contextually equivalent
normalize_sound      -- reconstructed named output is contextually equivalent to the input
isSame_sound         -- successful named comparison gives contextual equivalence at a common sort
isImplying_sound     -- successful named implication comparison gives an Ordered αβη proof
```

Thus formula normalization is justified in both directions, and normalizing
inside a term or a higher-order argument is also justified. No completeness or
uniqueness-of-normal-form claim is required. The proofs use only the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

### Correspondence with Scala

- `refineFactor` implements `treatChild`: it flattens conjunctions and uses the
  original conjunction as context to refine a negative conjunction. Both outer
  polarities follow Scala's comparison directions.
- `reduceList` retains Scala's block reversal and accepted/remaining traversal.
  A factor is removed only when the other factors imply it.
- `reduce` assembles the factors and performs contradiction detection. The
  empty and singleton cases are handled by `assemble`.
- `computeNormalForm` normalizes every child, including beneath arbitrary
  applications and lambdas, then simplifies the enclosing constructor.
- Equality uses equivalence of its normalized operands to reduce to truth;
  otherwise it receives a deterministic orientation. Universal quantification
  over truth or falsehood reduces to that constant.

The representation choices from milestone 1 remain: zero-based indices count
binders **of the same sort**, matching `Lambda.Term`; negation is a formula-only
constructor, and comparison passes polarity separately. These differ from
Scala's internal layout without changing the intended comparison rules.

The uncached definitions remain the specification. Identity shortcuts compare erased
Lambda terms. Equality orientation compares the constructors and fields
of `Lambda.RawTerm` directly, retaining all variable and argument sorts, rather than
using Scala's allocated `uniqueKey`s; it produces the same orientation
for either operand order. The cached implementation reuses these typed terms and
explicit-sort syntax trees. It preserves the ordering exactly; replacing it with
allocated IDs could change the specified output. Structural hashes are still
computed from trees; this milestone does not introduce hash-consing or claim
constant-time key operations. Comparisons of the resulting normal forms still
use `latticesEQ`, including commutativity.

### Public expression interface

Import `Lisa.Orthologic.Expression` for execution, or
`Lisa.Orthologic.ExpressionSoundness` for its proof guarantees. All three
operations are in the `Lisa.Orthologic` namespace:

```lean
normalize  : Expr → Option Expr
isSame     : Expr → Expr → Option Bool
isImplying : Expr → Expr → Option Bool
```

`SomeExpr` packages an internal expression with its sort; it does not assert
normality and also serves as the key type for unnormalized subtrees.
`prepare` returns such a package containing the normalized expression. It uses
`Lambda.interpretNamed`, `Lambda.normalize`, `SimpleExpr.ofTerm`, and
`computeNormalForm`, in that order. Comparisons consume these internal results
directly; only `normalize` reconstructs names for its output. There is no second
elaboration or normalization of reconstructed expressions during comparison.

`normalize` and `isSame` return `none` exactly when an input is ill-sorted.
Different well-sorted input sorts give `some false` for `isSame`.
`isImplying` returns `none` unless both inputs have proposition sort.
A `some false` answer is a failed comparison, not a claim of unprovability.

The translation expands disjunction, implication, biconditional, existential
quantification, and falsehood into conjunction, negation, and universal
quantification. Other applications and lambdas are traversed recursively,
including formulas inside epsilon terms and higher-order arguments.
Eta-long canonicalization exposes lambda arguments to quantifiers and supports
partially applied logical constants. Indices keep the Lambda package's per-sort
meaning throughout; soundness covers reconstruction with fresh binder names.

`prepare_alphaBetaEta` proves identical internal output for well-sorted
αβη-equivalent inputs, and `isSame_of_alphaBetaEta` proves they are accepted.
`normalize_formula_sound` and `isSame_formula_sound` give Ordered αβη proofs in
both directions; `isImplying_sound` gives a proof in the implication direction.
Function-sort equivalence is expressed by `ContextEq`, so it remains usable
inside arbitrary well-sorted formula contexts.

### Verified memoization

Import `Lisa.Orthologic.Cached`, or `CachedSoundness` for the Ordered guarantees.
`Cached.normalize`, `Cached.isSame`, and `Cached.isImplying` accept the same inputs
as the uncached entry points plus an optional cache configuration. They start
with an empty cache. To share work between queries, use the corresponding
`normalizeMemo`, `isSameMemo`, and `isImplyingMemo` operations:

```lean
let (answer, cache) := (Cached.isSameMemo p q).run ({} : Cached.Cache)
let (nextAnswer, cache) := (Cached.isImplyingMemo q r).run cache
-- answer.val and nextAnswer.val are Option Bool.
```

Each cached value includes a proof that it is exactly the uncached result.
Lean erases that proof during compilation. The `*_eq` and `*Memo_eq` theorems
therefore cover both acceptance and rejection, malformed input, all configuration
choices, and any well-typed initial cache. Soundness still targets actual
`Ordered.AlphaBetaEtaProof` derivations.

The session retains:

- Named preparation results, including `none`, so repeated input avoids
  elaboration and αβη normalization as well as OL normalization.
- Normal forms of every visited subtree, shared beneath quantifiers, terms and
  higher-order applications.
- Recursive comparison results, including `false`. Keys distinguish equivalence
  from directed comparison and retain both polarities and relevant sorts.
- Lambda terms used by identity shortcuts and explicit-sort syntax used to orient equality.

Keys use exact internal syntax. Erasure alone is insufficient: an explicit
application of `and` and the corresponding conjunction node can erase to the
same term while taking different paths through the normalizer. Hash collisions
are resolved by proved structural equality, never treated as equality themselves.

The caller owns the cache and its lifetime. There is no global cache, fuel or
eviction policy. `Config` can independently disable the four categories, and
`Stats` records hits and misses. Clearing a session simply starts a fresh cache.

The two cached comparisons are mutually recursive functions. Their numeric
termination parameters are erased by compilation; the generated C contains no
calls to `SimpleExpr.size`. Branch comments identify the syntax cases and their
polarity requirements. Equality orientation uses the structural order in
`StructuralOrder.lean`; its choice of operand order may differ from the former
printed-string order, while normalization soundness and exact cached/uncached
agreement remain proved.

### Checker integration and archive

The checker and binary reader now use `Cached.isSame` and `Cached.isImplying`
through a single positive-test interface. `Matching`, fallback selection,
Combined, Quantified, Replay, and the old reference algebra are absent from the
active import graph. Their sources and tests are preserved in
[Archive/Orthologic](../../Archive/Orthologic/README.md).

[Checker/ProofRelation.lean](../Checker/ProofRelation.lean) expresses the
certificate relation using actual Ordered αβη proofs and contextual equivalence.
Its preorder and congruence properties follow from proof steps. It is not the
algorithm's acceptance relation and has no decidability instance.
[Checker/Encoding.lean](../Checker/Encoding.lean) proves the wire-list/finite-set
bridge directly in that relation. `Test P` supplies only `ok = true → P`;
rejected comparisons are never treated as proofs of negation.

`Checked.sound` and `ClosedChecked.sound` in
[Checker/Soundness.lean](../Checker/Soundness.lean) finish the connection to
`Ordered.AlphaBetaEtaProof`. Discharge retains assumptions whose equivalence was
not established by the executable test. A derived `weakenAssumptions` lemma
justifies this conservative dependency tracking without changing any proof rule.

The checker uses recursive memoization within each expression comparison. It
does not yet share a cache across separate rule-condition tests or proof steps.
The CLI has one backend, no comparison budget, and no backend-selection options.
See [the checker guide](../Checker/README.md) for the API and CLI changes.

**Validation:** `lake build Lisa lisa-checker Tests` passes.
The normalization regressions include 185 propositional samples checked under
all eight Boolean valuations (1,480 checks), alongside quantifier, higher-order,
epsilon, binding, and equality-orientation cases. The new proof files contain
no `sorry` or added axioms. The named pipeline additionally checks 110
propositional expressions under all eight Boolean valuations (880 checks),
as well as αβη followed by OL, existential duality, partial logical applications,
epsilon nesting, mixed-sort binders, identifier collisions, and malformed input.
Memoization tests compare cached and uncached answers across all 16 policies,
check both polarities and directions, and verify that repeated positive,
negative and malformed queries avoid recomputation. Shared-subtree tests check
internal cache hits, and a forced-collision table checks exact key separation.
The cached agreement and soundness theorems use only the same standard Lean
axioms listed above.
All checker rule tests, substitution checks, binary-format tests and the original
51-step Scala export pass with the new pipeline. Integration tests additionally
cover αβη followed by OL, quantified implication, formulas inside epsilon,
higher-order arguments, permutations/duplicates, malformed input and discharge
with an equivalence not recognized by OL. The retired substitution-format
diagnostic remains unchanged. Old-backend-specific tests are archived; maintained
syntax and proof-system tests remain active.
No proof-system rule was changed in milestones 2–5.

**Subsequent binary integration:** the new substitution rules now have wire
tags 33 and 34, specified in [Checker/BINARY_FORMAT.md](../Checker/BINARY_FORMAT.md).
The stored `MGT024` regression has a migrated 42-step copy that checks
successfully; the unchanged original still tests the retired-tag diagnostic.
Substitution rule tests also exercise both streams, including paged input,
freshness rejection and preservation of both premises' dependencies.

## Objective

Implement one LambdaFOL equivalence checker organized like [`OLEquivalenceChecker.scala`](../../OLEquivalenceChecker.scala), with OL normalization at its centre. Replace the separate Combined, Quantified, and Replay backends and the checker's Matching machinery.

The public pipeline is:

1. Canonicalize expressions by alpha-beta-eta equivalence using the existing Lambda package.
2. Apply OL normalization extended to LambdaFOL. Its internal lattice comparison traverses quantifiers monotonically and other constructors through equivalence.
3. Compare the results with `latticesEQ`.

The final operation remains lattice equality, including comparison independent of conjunction/disjunction ordering and memoized comparisons. We do not require or claim a theorem that normalized forms are unique modulo commutativity. Completeness with respect to ortholattices is not a goal; soundness with respect to the Ordered proof system is.

## 1. Keep alpha-beta-eta canonicalization at the entry point

Reuse the existing total normalization for well-sorted expressions. Keep malformed-expression handling explicit.

The OL stage receives canonicalized expressions rather than running another fuel-based beta reducer. Check that translating and reconstructing internal expressions preserves the binding and canonicalization invariants needed by subsequent operations.

## 2. Use one internal LambdaFOL representation

Follow Scala's `SimpleExpression`: polarized conjunctions, quantifiers, equality, applications, lambdas, variables, and constants. Represent binding independently of chosen variable names.

Retain formulas occurring inside arbitrary terms. For example, a formula inside an epsilon term must remain accessible to normalization. The internal representation is an implementation detail, not another independently selectable comparison relation.

Choose the exact representation after checking which existing syntax and binding utilities can be reused. Preserve sorting guarantees where practical; avoid rebuilding unnecessary context machinery.

## 3. Define lattice comparison and equivalence together

Implement the Scala organization of `latticesLEQ` and `latticesEQ`:

- Lattice cases compare conjunctions, disjunctions, truth, and falsehood.
- Quantifiers compare their bodies monotonically; negative polarity reverses the comparison direction. Existentials can be represented through duality, as in Scala.
- Applications and other nonlogical constructors compare their components by equivalence, not one-way implication.
- Equality comparison accounts for symmetry.
- `latticesEQ` uses identity shortcuts, bidirectional comparison for formulas, and componentwise equivalence for other sorts.

These operations belong to one algorithm. They are not the current separate Combined and Quantified backends.

Prove termination using an appropriate measure on the compared expressions. Check recursive calls involving polarity reversal and component comparisons explicitly. Remove the configurable quantifier-depth bound rather than carrying it into the new interface.

## 4. Build normalization around comparison

Port the following Scala components and reuse existing Lean proofs where the algorithms match:

| Scala component | Intended role |
| --- | --- |
| `reduceList` | Flatten conjunctions and remove redundant components using lattice comparison. |
| `reduce` | Reconstruct a reduced conjunction or disjunction. |
| `checkForContradiction` | Detect collapse to truth or falsehood. |
| `computeNormalForm` | Normalize children, then simplify their enclosing expression. |

Include normalization beneath applications and lambdas, quantifier simplification, and equality reflexivity and symmetry. Establish termination separately for normalization and its calls into comparison; do not assume normalization is merely structural if its reconstruction steps introduce additional work.

The existing `Orthologic/Normalize.lean` and `Antichain.lean` are sources of reusable propositional algorithms and proofs. `Combined/Normalize.lean`, `Combined/Quantified.lean`, and the contextual comparison modules contain relevant behavior currently distributed across separate components.

## 5. Prove soundness in Ordered

For well-sorted formulas, the intended comparison theorem has the shape:

```lean
latticesLEQ p q = true →
  Nonempty (Ordered.ProofTree AlphaBetaEta {p} {q})
```

For an internal syntax, state this through its interpretation back into expressions. Normalization must preserve provable equivalence in both directions.

The target is Ordered instantiated with alpha-beta-eta equivalence. Soundness in Ordered instantiated with the algorithm's own accepted comparisons would not establish that the additional comparisons are justified.

Prove the constructor cases incrementally:

- Propositional transformations use the logical rules.
- Quantifier monotonicity uses the quantifier rules, with explicit freshness and binding arguments.
- For non-formula expressions, formulate and prove the contextual replacement guarantee required by application and equality.
- Check that the existing substitution rules justify equivalence beneath arbitrary applications, including epsilon arguments. Do not replace this obligation by an axiom in a reference expression calculus.

The current proofs into `ExpressionOrder.Derives` do not by themselves discharge this goal. Reuse their reasoning where appropriate, but establish the connection to actual proof steps.

If a constructor requires stronger proof-system principles, or a proposed simplification materially increases complexity, stop and explain the issue before changing the design.

## 6. Expose one public interface

- `normalize`: alpha-beta-eta canonicalization followed by extended OL normalization.
- `isSame`: normalize both expressions, then call `latticesEQ`.
- `isImplying`: normalize both formulas, then call `latticesLEQ`.

Add memoization for normalization and pairwise comparisons after the uncached definitions and their soundness are established. Prove that caching preserves results. Do not assume that an incomplete algorithm's acceptance relation is transitive without proving it; keep executable success and its logical soundness clearly distinguished where necessary.

## 7. Integrate and remove obsolete alternatives

Use the single interface for checker matching and sequent comparisons. Remove:

- the source/target selection through `Matching`;
- separate Combined and Quantified checker backends;
- Replay's union of their answers;
- reference-algebra and completeness infrastructure that becomes unused.

Reuse `OrderedComparison` for proof translation once the required admissibility theorem is available. Adapt checker certificates and interfaces to the soundness guarantees actually established.

Keep the existing implementation available while developing the replacement.
After migrating its callers, preserve obsolete components in the dedicated
`Archive/Orthologic` source tree and exclude them from active builds.

## Tentative file organization

```text
Lisa/Orthologic/
  Syntax.lean          -- internal polarized LambdaFOL expressions
  Comparison.lean      -- latticesLEQ and latticesEQ
  StructuralOrder.lean -- deterministic orientation of equality operands
  Normalization.lean   -- reduction and computeNormalForm
  Provability.lean     -- provability definitions and constructor lemmas
  Expression.lean      -- conversion from Expr and public interface
  Cached.lean          -- memoized implementation
```

These are tentative responsibilities, not a requirement to overwrite existing files or force cyclic dependencies. Conversion and supporting soundness lemmas may need to precede the final public interface.

## Milestones and validation

1. Establish the internal representation, binding conventions, and comparison definitions. Prove quantifier and application soundness first: these settle the principal risks.
2. Implement the OL normalizer and prove its transformations preserve equivalence.
3. Connect alpha-beta-eta normalization and the public expression interface.
4. Add verified memoization.
5. Migrate the checker, remove the alternate backends, and update documentation.

At each milestone compile the affected modules. Exercise propositional simplification, quantifier monotonicity, alpha-renaming invariance, formulas inside terms, equality symmetry/reflexivity, and negative comparisons. Compare representative behavior with the Scala reference, distinguishing intentional differences from regressions. Finish by building the project and its existing tests.

No completeness or uniqueness-of-normal-forms proof is required to complete this work.

## First milestone: application soundness audit

**Update:** The agreed two-premise simultaneous substitution rule is now implemented in the three proof systems and checker; see [the rule-change plan](../SUBSTITUTION_RULE_PLAN.md). The old quantified instructions and their compatibility code have been removed. `OLCongruenceTests.applicationCongruence` in [Tests/OLCongruence.lean](../../Tests/OLCongruence.lean) proves the motivating higher-order equivalence below in `Ordered AlphaBetaEta`. The following audit records the restriction that prompted this change; it applies to the old rule. The general recursive comparison and normalization soundness proofs are now complete; see the implementation status above.

The initial audit found an obligation that had to be resolved before adopting all Scala constructor cases. De Bruijn binding is not the obstacle identified here.

The former `SubstContext.wellSorted` condition restricted substitution parameters to sorts accepted by `LSort.isFunctional` or `LSort.isPredicate`. Those are individuals, formulas, and functions/predicates taking only individual arguments. In particular, `prop >> prop` is rejected by both predicates. That condition has since been removed. The remainder of this audit describes the situation before that rule change.

Consider a schematic symbol `h : (prop → prop) → prop` and the well-sorted formulas:

```text
h (λx : prop. x ∧ top)
h (λx : prop. x)
```

Scala's normalization reduces the conjunction beneath the lambda, making the arguments agree. The proposed Lean comparison therefore needs a justification for replacing these function arguments. They are not identified merely by alpha-beta-eta conversion. The existing equality-substitution rule cannot directly use a parameter of their sort, and `SubstPair.liftEq` cannot simply be generalized by quantifying over propositions: the proof system quantifies only over individuals.

Lean checks confirmed that both example applications are formulas and that no well-sorted substitution context can contain a parameter of sort `prop → prop`. This is a verified restriction on the existing rule, not a proof that no indirect derivation is possible.

The initial decision was whether to derive a stronger replacement theorem, extend the proof system, or restrict higher-order normalization. The user chose the general two-premise substitution rule. The current proofs derive congruence from that rule, rather than assuming it in the old reference calculus.

### Investigation of indirect derivations

The audit used Lean checks to establish:

- Both directions of the body comparison `x ∧ top` versus `x` have actual derivations in `Ordered AlphaBetaEta`.
- The applications `h f` and `h g` above are not alpha-beta-eta equivalent, using the existing normalization characterization.
- Under the former restriction, a well-sorted substitution context could not have a parameter of sort `prop → prop`.
- Substituting `x ∧ top` for `p` in `λx. p` leaves `x` free: capture avoidance prevents this from producing `λx. x ∧ top`.

Thus replacing a propositional parameter and then using schematic instantiation does not implement the required binder capture. `instSchema` applies the same sort-preserving, capture-avoiding substitution to a derivation; it is not an abstraction-congruence rule. The existing pointwise-equality construction handles individual-domain predicates but does not supply a formula expressing pointwise equality over propositions or higher-order inputs.

No general higher-order replacement theorem was found for the former rules. Those checks were not a formal nonderivability result. With the subsequently agreed substitution rule, `ContextEq.app` and `ContextEq.lam` now derive the required congruence. They concern expression constructors and binding, not arbitrary Lean functions `Expr → Expr`.

### Historical two-premise substitution audit

The upstream development version immediately preceding [commit `5272ab1`](https://github.com/epfl-lara/lisa/commit/5272ab11d196dc0f9f3ede7237613343dffce964) contains a two-premise rule that applies the compared expressions to an explicit list of variables and checks equality/equivalence of those applications. It checks freshness in the equality premise's other formulas, but not freshness for the compared expressions themselves or distinctness of the argument variables.

On October 22, 2026, the unmodified historical kernel at parent commit `d648a97de00ec016dd00225aad1ddc80357d31fe` was compiled and run with Scala 3.5.1. Two independent counterexamples were accepted, each with zero imports and `usesSorry = false`:

1. **A comparison parameter free in a replacement.** Let `s = λu. u`, `t = λu. a`, and supply `[a]` as the parameter list. The equality premise compares `s(a)` and `t(a)`, both beta-reducing to `a`. The rule then allows replacement in `C[F] = (F(b) = b)`, changing the reflexive theorem `b = b` into `a = b`. The parameter `a` needed to be fresh for `t` as well as for the remaining equality-premise formulas.
2. **Repeated comparison parameters.** Let `s = λu. λv. v` and `t = λu. λv. u`, and supply `[a, a]`. The equality premise again reduces to `a = a`, although the functions disagree off the diagonal. Replacing in `C[F] = (F(a)(b) = b)` again derives arbitrary `a = b`. The parameters needed to be pairwise distinct. Here the compared expressions are closed, so this is independent of the first bug.

Each reproduction uses two reflexivity steps, beta conversions, and one `RightSubstEq` step. Source and harness are retained in the local research directory `.lake/old-kernel/`; the harness is `SubstitutionAudit.scala`. These are findings about the removed development implementation, not a claim about the current upstream checker.

The same harness also successfully derives `∀z. f(z)=g(z), P(f(a)) ⊢ P(g(a))` using the historical two-premise rule. Thus universally quantified equality assumptions were usable: first instantiate the equality with a fresh variable, then use that variable in the comparison premise.

For individual-domain functions and predicates, the correctly formulated two-premise rule and the quantified-assumption rule can simulate each other using quantifier introduction/elimination and cut. The quantified version packages more work into a single step and supports a list of replacements directly; that does not by itself establish greater derivability. A repaired general rule must use pairwise-distinct, correctly sorted parameters, fresh for the compared expressions and for the equality premise's other formulas, and compare fully applied base-sort results.

The historical change was authored October 24, 2024 and reached main through PR #234 in July 2025. No explanatory commit comment or PR discussion was found tying the change to either counterexample. The actual bugs are confirmed; the author's motivation remains undocumented in the material inspected. The intended higher-order rule with suitable side conditions remains distinct from this faulty implementation.
