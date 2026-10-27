# Syntactic translation to first order logic with epsilon

Updated 26 October 2026. This replaces the plan to obtain the final reduction
through models and an external completeness theorem. The independent epsilon
target, expression representation, and full equivalence of provability are
implemented. A/B also have equivalence theorems for the new `.fol` target.

## Implementation status

The active entry point is `Epsilon.lean`, also imported by `C.lean`.

| Obligation | Current result |
| --- | --- |
| Match target epsilon extensionality to the actual source | `SourceEpsilon.epsilonExt` derives it in Ordered, retaining residual contexts. |
| Independent first-order syntax and calculus | `PureSyntax.lean`, `PureBinding.lean`, `PureCalculus.lean`; epsilon is enabled only in `.epsilon` mode. |
| Inclusion of FOL proofs | `PureInclusion.ProofTree.mapMode` maps complete derivations and transports freshness. |
| Source canonical-form shape with epsilon | `EpsilonShape.canonical_lamfol`, including formulas inside epsilon terms. |
| Total, conversion-invariant readback | `EpsilonReadback.lean` and `EpsilonReadbackTotal.lean`. |
| Expression representation | `C.formula_representation`, `C.term_representation`, and `C.formula_provable_equivalence`. |
| Embedding and individual binding/substitution | `PureEmbedding.lean`, `PureEmbeddingBinding.lean`, `PureEmbeddingReplacement.lean`; all constructors, including epsilon, are covered. |
| Arbitrary source derivations and generalized simultaneous substitution | `Syntactic.ordered_toPure` transports every actual Ordered rule. `substitution_rule_equiv` handles the actual `SubstRule`, retaining simultaneous replacements and residual contexts. |
| A/B target migration | `FOL.lean` exports `a_iff_pure_fol`, `b_iff_pure_fol`, `FOL.fromA`, and `FOL.fromB`. Their proven implementation is retained behind `MathlibSyntax.provable_iff`, a two-way syntactic bridge. |
| Reverse derivation translation | `PureEmbedding.toOrdered` transports every target rule, deriving epsilon extensionality using the existing source rule. |
| Final equivalence of provability | `ordered_iff_pure_epsilon`, exported as `C.iff_pure`. It compares the original source sequent with its canonical first-order readback. |
| Previous semantic/completeness route | Preserved separately in `Reference/` and `Archive/SCLambdaCompleteness/`; absent from the active reduction imports. |

The common calculus has namespace `PureSyntax`; the old `Pure` namespace remains
as a compatibility implementation for A/B and the archived semantic results.
Instead of rewriting all existing A/B clients, `MathlibSyntax.lean` and
`MathlibCalculus.lean` translate their syntax and proofs in both directions.
`PureEncodings.lean` derives the rules for Mathlib's connective encodings.
This is a deliberate change from the initial wholesale internal migration below:
the new A/B end theorems use `.fol`, while their established internal proofs remain
available. No epsilon theorem depends on this proof bridge.

The new target uses
explicit connectives, so its expression roundtrip is alpha-beta-eta equivalence,
without the old detour through logically equivalent connective encodings.

`Tests/PureEpsilon.lean` exercises nested epsilon and quantifiers, shadowing,
free variables, higher-order beta reduction, capture avoidance, simultaneous
replacement, witness introduction, contextual epsilon congruence, FOL inclusion,
and axiom audits. It also checks complete proof transport with a higher-order
intermediate cut, simultaneous replacement images mentioning each other's
parameters, contextual epsilon extensionality, and schematic instantiation
introducing epsilon. The final C and A/B theorems and the difficult substitution
lemma use only `propext`, `Classical.choice`, and `Quot.sound`.

Verification completed: `lake build Lisa lisa-checker Tests` passed (1,802 jobs),
including the existing checker and serialized-corpus regressions. The source
audit found no `sorry`, `admit`, or additional axiom declarations in the reduction.

### How to read the completed proof

1. `PureSyntax.lean` and `PureCalculus.lean`: the independent target language and rules.
2. `EpsilonShape.lean`, `EpsilonReadback.lean`, `EpsilonRepresentation.lean`: normalize,
   read a first-order formula, and prove that it represents the original expression.
3. `SyntacticRelation.lean`: relate complete expressions using target equality or
   equivalence proofs; at arrow sorts, compare their applications to related arguments.
4. `SyntacticConnectives.lean` through `SyntacticGrounding.lean`: logical constants
   preserve that relation, including epsilon. Every admitted expression relates to itself.
5. `SyntacticPointwise.lean`, `SyntacticParameters.lean`, `SyntacticContext.lean`,
   `SyntacticRule.lean`: turn the source rule's independent pointwise comparisons
   into a proof of equivalence of the simultaneously instantiated formula context.
6. `OrderedToPure.lean`: the induction over all Ordered constructors.
   `SyntacticQuantifiers.lean` chooses fresh readback names; `SyntacticEncoding.lean`
   transports the actual whole-sequent restatement rule.
7. `PureToOrdered.lean`: reverse induction, using ordinary source derivations.
8. `EpsilonConservativity.lean`: grounding fixes the concluding boundary formulas;
   one shared name decoding and cuts recover the exact original sequent on return.
   `C.iff_pure` is the public endpoint.
9. `FOL.lean`: the earlier A/B results in the common syntax with epsilon disabled.

The target will retain epsilon as a first-order term binder. We remove lambda
abstractions and higher-order application by canonicalization, while preserving
the formulas inside epsilon terms. For example:

```text
epsilon (lambda x. P x)  translates to  epsilon x. P(x)
```

The source remains the actual `Ordered.ProofTree AlphaBetaEta`. No change to
the checker, Orthologic, or the source proof rules is planned. Epsilon elimination
can be a separate later result about the first-order target.

## 1. The results to obtain

There are two results, with different purposes.

**Expression representation.** For each formula `p` in the intended fragment,
construct a first-order formula `read p` with epsilon and prove:

```text
AlphaBetaEta p (embed (read p))
```

Here `read` first computes the beta-normal, eta-long form. The embedding turns
first-order binders back into Lisa's lambda representation. This gives, in the
source calculus, a proof of `p iff embed (read p)`. Establish the analogous
roundtrip for individual terms. With explicit target connectives, the intended
roundtrip can use conversion rather than proofs comparing different encodings
of conjunction and disjunction.

**Proof translation.** For sorted contexts in that fragment, prove:

```text
Nonempty (Ordered.ProofTree AlphaBetaEta Gamma Delta)
  iff
Pure.Provable emptyTheory (readContext Gamma) (readContext Delta)
```

Implement transformations of derivations in both directions, then state the
provability equivalence. No semantic-validity premise or completeness assumption
belongs in the theorem.

The fragment initially keeps the current boundary restriction: free variables
have sort `ind` or `prop`, and constants are first-order symbols or the recognized
logical constants, now including epsilon. Free proposition names become nullary
predicate symbols. Higher-order bound variables and redexes are allowed. There
is no corresponding restriction on intermediate formulas of a source proof.

An arbitrary free symbol taking a predicate or function as an argument is outside
this boundary. Grounding such a symbol during proof translation is not a proof
that the original formula is equivalent to its grounded form. Preserving free
first-order function and predicate schematics as signature symbols is a possible
later enlargement; the first implementation must not silently enlarge the
existing boundary theorem.

Assumptions remain in the antecedent. This does not assert conservativity over
epsilon-free FOL, or closure of an arbitrary fixed theory under new instances of
its axiom schemas.

## 2. An independent first-order target

Mathlib's term datatype cannot be extended with an epsilon constructor: terms
and formulas must now be mutually recursive. Introduce a small independent
syntax in `PureSyntax.lean`, and keep `Pure.lean` for its proof calculus.

```text
Term    := variable | function(arguments) | epsilon Formula
Formula := predicate(arguments) | Term = Term
         | top | bottom | not Formula
         | Formula and Formula | Formula or Formula
         | Formula implies Formula | Formula iff Formula
         | forall Formula | exists Formula
```

Function and predicate arguments are individual terms only. Quantifiers and
epsilon bind individual variables only. There are no arrow sorts, lambda
constructors, or arbitrary application constructors in this syntax.

Keep the current free-variable identifiers and bound-variable convention: free
variables are a separate parameter, and a natural-number scope records individual
bound slots using `Fin n`. Entering a binder adds the last slot, as in the current
Mathlib-facing reader. This avoids also changing the existing index translation.
There is no context of simple types `Gamma`. Mathlib's arity-indexed `Language`
can still supply the signature; its term and formula datatypes no longer supply
the representation.

Use explicit logical constructors. The current Mathlib encoding of derived
connectives causes extra logical roundtrip proofs; reproducing that encoding is
unnecessary for the new independent target.

Implement only the binding operations needed by the translation: relabeling,
capture-avoiding simultaneous individual substitution, opening/closing a named
variable, and free-variable support. Their proofs must recurse mutually through
terms and formulas, including substitution inside epsilon bodies.

### Preserve the completed A and B results

The current A and B calculi have no epsilon proof rule. Giving their target new
rules and retaining their old equivalence statements would leave the reverse
directions unproved, even for epsilon-free concluding sequents.

Use one shared syntax and calculus definition with two explicit modes, `fol`
and `epsilon`. In `fol` mode neither epsilon terms nor epsilon rules can be
constructed. In `epsilon` mode they can. This is a single fixed distinction,
not a general framework for configurable logics.

Expose `Pure` aliases for the epsilon mode and `Pure.FOL` aliases for the original
fragment. Port the existing A/B results to `Pure.FOL`, with theorem names or
statements making that endpoint explicit. Ordinary rules and their structural
lemmas are shared. Prove inclusion from the FOL mode to the epsilon mode.

The resulting organization is:

```text
B -> A -> Pure.FOL -> Pure
Ordered AlphaBetaEta <-> Pure       on the stated boundary
```

There is no C-to-existing-B epsilon-elimination step in this plan. The final
translation goes directly to `Pure`. A and B remain the proved earlier stages
and sources of reusable translation lemmas.

## 3. The epsilon rules the target needs

Keep the ordinary first-order sequent rules and individual equality substitution.
Add the witness rule in the form already used by `Ordered.rightEpsilon`:

```text
Gamma |- phi[x := t], Delta
-------------------------------------------
Gamma |- phi[x := epsilon x. phi], Delta
```

Also include extensionality of epsilon:

```text
Theta |- phi iff psi, Xi
-------------------------------------------
Theta |- (epsilon x. phi) = (epsilon x. psi), Xi

x is not free in Theta or Xi
```

This second rule is necessary to match the current source system. Its generalized
substitution rule can replace `lambda x. phi` by `lambda x. psi` inside epsilon
using a proof of pointwise equivalence. The witness rule alone does not supply
that replacement principle. Extensionality here is a first-order rule about two
individual epsilon terms; it introduces no function equality into the target.

Before relying on this target rule, construct its derivation in `Ordered
AlphaBetaEta` from the existing generalized substitution rule. Keep the proof's
assumptions and succedent: an unconditional special case is insufficient.

Then derive congruence of first-order terms and formulas from equality,
propositional equivalence, and this epsilon rule. The argument entering epsilon
is a formula, so the two congruence proofs must be mutual. Binder cases carry
the appropriate freshness conditions. These lemmas justify replacements below
epsilon without copying the entire higher-order source rule into `Pure`.

## 4. Extend canonicalization and readback

Retain the existing lambda normalizer and its proofs. The change belongs in the
characterization and reading of its output.

1. Add epsilon at its exact identifier and sort to the permitted constants in
   the epsilon mode. Keep the FOL mode's current constant classification.
2. Make `FirstOrderShape.Individual` and `FirstOrderShape.Formula` mutually
   recursive. The new individual case is `epsilon (lambda x : ind. p)` for a
   first-order formula body `p`.
3. Extend the normalization shape argument, replacement closure, and normal-form
   stability to that case. Retain the result that all remaining lambda binders
   at ground sorts occur immediately under quantifiers or epsilon.
4. Make readback mutually recursive through individual terms and formulas.
   Reading epsilon calls the formula reader under one more individual binder.
   It must never hide an unsupported body inside an opaque function symbol.
5. Extend totality, conversion invariance, support, binding, and individual
   substitution lemmas. In particular, reading a substitution into an epsilon
   body must equal substituting into the corresponding target binder.
6. Extend embedding in the reverse direction and prove the expression roundtrip.
   Preserve complete identifiers, schematic/constant distinctions, and recognition
   of reserved symbols at their exact sorts. State roundtrips for the actual
   translation signature/image rather than assuming arbitrary target symbols
   cannot collide with Lisa's reserved logical names.

In the epsilon mode, grounding must preserve epsilon. It can use the closed term
`epsilon x. top` as the default individual, avoiding the additional `_default`
constant used by the old translation. Default propositions remain `top` and
default functions remain constant lambda expressions. Grounding still changes
only symbols outside the chosen fragment; it is the identity at the boundary.

## 5. Translate the actual source derivations

Ordinary propositional rules, quantifiers, equality reflexivity, cut, weakening,
and epsilon transport by the syntactic readback laws. Handle `restateWeaken`
using conversion invariance of the encoded sequent and the existing syntactic
sequent-encoding derivations. Its hypothesis is on the whole encoded sequent;
it must not be replaced by an assumption of pairwise matching formulas.

Two cases need more than extending the current A proof induction.

### Schematic instantiation

The translator must be uniform in admissible substitutions for source symbols.
For an `instSchema` node, compose the requested substitution with the translation
assignment and invoke the induction hypothesis. The existing B admissibility
proof supplies the capture-avoidance and fresh-renaming pattern, but `B.toA`
cannot simply be applied to a C proof containing additional rules.

### Generalized simultaneous substitution

The proof of a pointwise comparison must remain usable at arbitrary arguments
of the indicated sorts. For example, if a comparison uses a fresh predicate
parameter `P`, the proof may need to be instantiated at an actual predicate
appearing in the main expression. Grounding `P` to a fixed default before this
step loses that information.

Strengthen the proof induction to provide translations under admissible symbol
assignments, including alternative assignments to fresh comparison parameters.
Freshness ensures that these alternatives leave `Theta` and `Xi` unchanged.
Do not require comparison parameters to be fresh for the other premise's
contexts `Gamma` and `Delta`.

The proposed transport lemma uses a syntactic relation by sort. At `ind`, its
evidence is a target derivation of equality; at `prop`, a derivation of logical
equivalence. At arrow sorts, its evidence describes how such derivations are
obtained on application to related arguments. These are metatheoretic statements
about expressions and proof trees, not models or new quantifiers in `Pure`.

Prove preservation through source constructors, substitution, and conversion.
Logical constants reduce to target proof rules; the epsilon case uses the
extensionality rule above. Use the translated comparison premise at fresh
arguments to build this evidence, then apply it to the source substitution
context. Finally reconstruct the two-premise target inference with its union
of contexts.

Keep all replacements simultaneous. In particular, a free variable in one
replacement image is not subsequently replaced by another entry. The existing
semantics proves this rule sound but is not a syntactic proof of this transport
lemma. This is the main feasibility obligation and should be prototyped early.

## 6. What survives and what becomes unnecessary

| Existing files | Planned treatment |
| --- | --- |
| `Lisa/Lambda/*`, `Lisa/AlphaBetaEta.lean`, `Lisa/Ordered.lean` | Keep. Reuse canonicalization, conversion and the actual source rules. |
| `A.lean`, `B.lean`, `AInstantiation.lean`, `BToPure.lean` | Preserve their proof systems and instantiation argument. Keep their equivalences about the FOL target mode. |
| `Pure.lean` | Replace the Mathlib syntax aliases by the shared independent syntax; retain the ordinary calculus and structural constructions, and add the two enabled epsilon rules. |
| `Canonical.lean`, `CanonicalReduction.lean`, `FirstOrderShape.lean`, `FirstOrderNormalization.lean`, `Grounding.lean` | Reuse the construction; generalize fragment-dependent statements and add the mutual epsilon cases. |
| `Replacement.lean`, `NamedReplacement.lean`, `Instantiation.lean`, `Support.lean` | Retain general source binding/substitution machinery; audit which statements are independent of the target representation. |
| `FirstOrderReplacement.lean`, `Readback.lean`, `ReadbackTotal.lean`, `ReadbackSupport.lean`, `ReadbackBinding.lean`, `ReadbackReplacement.lean`, `ReadbackSubstitution.lean` | Port target operations and extend them through epsilon. Term and formula proofs become mutual where required. |
| `Translation.lean`, `TranslationBinding.lean`, `TranslationSubstitution.lean`, `AToPure.lean`, `Concrete.lean` | Retain the A-to-FOL construction, updating its target API. Extract common lemmas for C; do not assume the A interface already handles C substitution. |
| `Embedding.lean`, `EmbeddingNamed.lean`, `EmbeddingRules.lean`, `EmbeddingSupport.lean`, `PureToA.lean` | Port the existing FOL embedding; add the epsilon-mode embedding into Ordered. |
| `BoundaryNames.lean`, `BoundaryBinding.lean`, `BoundaryLogic.lean`, `AtomicRoundtrip.lean`, `FormulaRoundtrip.lean`, `Conservativity.lean` | Reuse freshness and boundary arguments. Remove encoding-specific detours where explicit target connectives make the roundtrip a conversion proof. |
| `C.lean` | Become the entry point for the syntactic C translation and final theorem. Move its current semantic theorems to the optional semantics development. |

The following files were added for the semantic route and are **not needed by
this reduction**:

- `Model.lean`, `ModelExtension.lean`.
- `NamedSemantics.lean`, `ExpressionSemantics.lean`, `LogicalSemantics.lean`.
- `PointwiseSemantics.lean`, `SubstitutionSemantics.lean`, `SequentSemantics.lean`,
  `SubstitutionRuleSemantics.lean`.
- `OrderedSoundness.lean`, `PureSemantics.lean`.

Their soundness results remain valid for the definitions they were proved about.
Preserve them together as an optional/reference development, outside the active
reduction imports. `PureSemantics.lean` specifically concerns the old Mathlib
target; it must not be presented as soundness of the new target without a new
proof. If archiving it, retain the old target definition it needs as well.

The previous `Verification` package is now retained at
`Archive/SCLambdaCompleteness` and is unnecessary for this task:

- `Completeness/FoundationSyntax.lean` and `FoundationCompleteness.lean`.
- Its test and umbrella modules, Lake configuration, manifest, and toolchain file.
- The Foundation dependency and its documentation dependencies.

Archive that experiment for reference, with its dependency configuration, rather
than integrating it further. There is no need to implement Foundation-to-Pure
proof transport, model extension/readback correspondence, or a completeness
theorem. The root project already depends only on Mathlib, so removing the
separate experiment from the active plan does not change the checker's dependencies.

The existing `C.consistent` corollary is optional too; it is not a required step
in the syntactic translation. Preserve its statement with the semantic results.

## 7. Implementation sequence and checkpoints

1. **Confirm target rules against the source.** Derive epsilon extensionality
   with residual assumptions in Ordered. Fix the exact target substitution and
   binder interfaces. This tests the logical match before a broad migration.
2. **Build the independent target.** Implement the shared syntax, two modes,
   binding operations, ordinary sequent calculus, epsilon rules, and mutual
   congruence lemmas. Keep the old target available while its clients are ported.
3. **Prototype the difficult substitution transport.** Establish the strengthened
   induction interface and the syntactic relation by sort. Check applications to
   higher-order arguments and replacement below epsilon before claiming the
   remaining work is routine. If these require additional target rules, explain
   the exact missing derivation before changing the target.
4. **Port A/B and extend normalization/readback.** Recover the existing FOL
   theorems in the disabled mode. Prove epsilon-mode shape, totality, substitution,
   freshness and expression roundtrips. Consolidate duplicated arguments.
5. **Translate all Ordered rules.** Implement the uniform forward proof
   transformation, including schematic instantiation and simultaneous
   substitution. Implement the reverse target-to-Ordered transformation.
6. **Compose the final results and clean up.** Prove the formula representation
   theorem and sequent provability equivalence. Archive the semantic/completeness
   experiment, update imports and documentation, and remove superseded helpers
   only after their replacement clients compile.

The most substantial cost is changing the independent target syntax and proving
generalized substitution transport. Keeping epsilon removes the need for epsilon
elimination and completeness; it does not make these two syntactic obligations
automatic.

## 8. Verification

Compile in dependency order and retain all current A/B regressions. Add examples
that exercise obligations not covered by epsilon-free proofs:

- An epsilon term containing another epsilon term; a quantifier inside epsilon;
  epsilon inside a quantified formula; shadowing and free-variable preservation.
- A higher-order beta redex whose first-order normal form contains epsilon, and
  eta expansion of a predicate passed to epsilon.
- The witness rule from a genuine witness premise.
- Epsilon extensionality under nonempty `Theta` and `Xi`, with its precise
  freshness requirement.
- Generalized substitution under epsilon, function and proposition arguments,
  and simultaneous replacements whose images mention other parameters.
- Schematic instantiation introducing epsilon in an intermediate formula.
- The whole proof translation in both directions, with assumptions and arbitrary
  higher-order intermediate formulas, for representative first-order conclusions.
- FOL-mode examples and the explicit inclusion of FOL proofs into Pure.

Audit axioms of the final theorem and its key transport lemmas. No `sorry`,
completeness axiom, semantic interpretation hypothesis, or assumption that the
desired substitution transport already holds may remain. Finally run
`lake build Lisa lisa-checker Tests`; the executable should need no code changes.

The status table records the completed results. The implementation retains the
old A/B helpers behind the syntax compatibility bridge rather than replacing
them all. Further consolidation of those helpers is an optional cleanup, not
an assumption of any final theorem.
