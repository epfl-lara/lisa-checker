# Orders and proof systems in Lisa

This guide covers the next layer after [the Lambda package](Lambda/README.md): the interfaces for comparing expressions, two presentations of sequent proofs, and the translations between them.

The purpose of this layer is to describe **which proof steps the checker may accept and how flexible proof steps can be justified by more explicit ones**. It does not yet implement the concrete comparison algorithm or the executable checker.

## Reading order and dependencies

Read these files in this order:

1. [Order.lean](Order.lean): expression relations, context matching, and constructor-compatibility interfaces.
2. [Ordered.lean](Ordered.lean): explicit sequent rules, ordinary weakening, and order-based restatement.
3. [AlphaBetaEtaOrder.lean](AlphaBetaEtaOrder.lean): Ordered instantiated with alpha-beta-eta conversion.
4. [Weakened.lean](Weakened.lean): rules accepting flexible premise and conclusion contexts.
5. [OrderedEncoding.lean](OrderedEncoding.lean), then [OrderedComparison.lean](OrderedComparison.lean): sequent packing and translations between Ordered instances under admissibility.
6. [OrderedWeakened.lean](OrderedWeakened.lean): translations between Ordered and Weakened.
7. [OrderSimulation.lean](OrderSimulation.lean): transferring successful comparisons between different orders.

The local import graph is:

```text
Syntax → Order → Ordered → AlphaBetaEtaOrder ← AlphaBetaEta
           │       └→ Weakened
           └→ OrderSimulation

Ordered → OrderedEncoding
OrderedEncoding + OrderSimulation → OrderedComparison
Ordered + Weakened → OrderedWeakened
```

`OrderSimulation` can be read immediately after `Order`; its later position makes its purpose easier to appreciate. `AlphaBetaEtaOrder` supplies the baseline instance without defining another proof datatype.

[Orthologic/Basic.lean](Orthologic/Basic.lean), described below for background, is now needed only when reading the orthologic implementation. It is not a dependency of `Order.lean`.

## What a sequent and a proof tree mean

The notation

```text
Γ ⊢ Δ
```

represents a sequent with assumptions `Γ` and alternatives `Δ`. Informally, if all assumptions hold, at least one formula on the right holds. Both sides are `Finset Expr`, so order and repetitions of formulas are already forgotten.

**Here `Γ` is a finite set of formulas.** The current lambda package uses `Term s`, without a variable-context parameter.

The declarations

```lean
Ordered.AlphaBetaEtaProof Γ Δ
Ordered.ProofTree leq Γ Δ
Weakened.ProofTree leq Γ Δ
```

are types of derivation trees for that sequent. Their constructors are inference rules: constructing a tree requires supplying its premises and side conditions.

The trees live in `Type`. Therefore, the statement that a derivation exists is written `Nonempty (…ProofTree …)`. The equivalence theorems below compare existence of derivations, not literal equality of trees.

`Expr` is the original named syntax. It does not enforce sorting in its datatype, so the rules explicitly require `isFormula φ`, `isTerm t`, and `isFSet Γ` (every member of `Γ` is a formula).

## 1. Orthologic: the comparison algorithm

The active [Orthologic package](Orthologic/REORGANIZATION_PLAN.md) implements
αβη canonicalization followed by extended OL normalization and comparison.
Its soundness target is `Ordered AlphaBetaEta`, using actual inference rules.
The proof-system interfaces below do not depend on the algorithm or an algebra.

The previous ortholattice-based implementation is preserved in
[Archive/Orthologic](../Archive/Orthologic/README.md). It is excluded from active
builds. In particular, no ortholattice completeness assumption is needed by the
new checker.

## 2. Order: comparison and the laws needed by its consumers

Source: [Order.lean](Order.lean).

### An order starts as an arbitrary relation

```lean
abbrev ExprRel := Expr → Expr → Prop
```

This abbreviation alone imposes no reflexivity, transitivity, or antisymmetry. Those properties are requested separately where needed.

For a chosen relation `leq`:

```text
isSame leq p q := leq p q ∧ leq q p
```

This is comparison in both directions. It is not Lean equality, and it is not defined to be alpha-beta-eta conversion. A concrete order can recognize additional propositional relationships.

### Constructor compatibility, without logical identities

`ExprRel` is an expression relation. `RelationCongruence` requires preservation of
equivalence under implication and under equality of individual terms. These are
the two constructors needed by the correspondence proof. Other constructors
could be added, but are unnecessary: cuts and structural weakening handle larger
contexts. It imposes no logical identities. The diagonal relation satisfies it.

The proof systems supply structural weakening and logical rules themselves.
Their correspondence uses cuts with matched hypotheses to replace formulas in
contexts. It does not assume that adding context members gives a comparison
between encoded sequents.

### The checker supplies positive tests

[Checker/Interfaces.lean](Checker/Interfaces.lean) defines `Test P`: a Boolean
and a proof that success implies `P`. `Testable P` supplies such a test.
For expression comparisons the implementation calls the memoized OL pipeline.
For sorting and freshness, ordinary decidable tests suffice.

The relation in certificates, `Imported.Checker.ProofRelation`, is defined
using Ordered αβη derivations and contextual equivalence. Its transitivity is
proved by composing derivations; transitivity of algorithmic acceptance is not
assumed. A rejected comparison is not a disproof of the relation.

### Matching formulas and contexts

These predicates describe different strengths of matching. Their differences matter in `Weakened`:

| Predicate | Meaning |
|---|---|
| `ordContains leq p Γ` | Some member of `Γ` is order-equivalent to `p`. |
| `setLeq leq Γ Δ` | Every member of `Γ` has an order-equivalent member in `Δ`. |
| `containedExcept leq Γ Δ p` | Every member of `Γ` is order-equivalent to a member of `Δ` or to `p`. |
| `containedExceptEither leq Γ Δ p q` | Every member of `Γ` is order-equivalent to a member of `Δ`, to `p`, or to `q`. |

In particular, `setLeq` is inclusion **up to equivalence**, not pointwise one-way inequality. Both exception predicates use the same equivalence for retained and principal formulas.

Example: if the premise contains `{a, b, c}` and the conclusion retains `{c}`, then `containedExceptEither … {a,b,c} {c} a b` permits removing the two principal formulas. It would not permit silently dropping an unrelated `d`.

The lemmas at the end of `Order.lean` turn ordinary subset or set-difference facts into these predicates using reflexivity. The checker composes positive equivalence tests to establish these conditions.

### Comparing whole sequents

`sequentToFormula Γ Δ` encodes a sequent as:

```text
if Γ is empty:  disjunction Δ
otherwise:     conjunction Γ → disjunction Δ
```

Empty conjunction and disjunction have units `top` and `bot`. Nonempty folds start at their first formula: a singleton disjunction is `p`, not the syntax `bot ∨ p`.

Then:

```text
sequentLeq leq Γ Δ Γ' Δ'
  := leq (sequentToFormula Γ Δ) (sequentToFormula Γ' Δ')
```

This compares the entire sequent formula. It is different from matching the two contexts member by member.

The finite-set encodings are `noncomputable` because they use `Finset.toList`.
[Checker/Encoding.lean](Checker/Encoding.lean) defines `listSequentToFormula`
on input lists and proves `listSequent_same`: for well-sorted inputs, the list
and finite-set formulas are equivalent in `ProofRelation`. This is proved
using logical rules, including permutation and duplicate removal.

The generic proof systems still permit arbitrary expression relations.
`ProofOrder` is only a convenience bundle of a preorder and
`RelationCongruence`, used where these laws are needed. The checker separately
supplies the particular relation justified by Ordered αβη proofs.

## 3. Ordered: explicit logical rules with order-based structural steps

Source: [Ordered.lean](Ordered.lean).

### Substitution data shared by the proof systems

`SubstPair` contains a `source` and a `target` expression. `wellSorted` requires the source to be well-sorted and both computed sorts to agree.

`SubstPair.pointwiseEq` expresses the relationship needed to substitute one expression for the other. It applies both expressions to explicitly supplied fresh variables and compares their ground results. Examples, schematically:

```text
s, t : ind         → s = t
P, Q : prop        → P ↔ Q
f, g : ind → ind   → f x = g x
P, Q : ind → prop  → P x ↔ Q x
f, g : prop → prop → f p ↔ g p
```

These comparison variables are free parameters, not quantified variables. They must be distinct within each argument list and absent from the compared expressions' free variables. A second proof premise supplies the comparison, or the conjunction of comparisons for a batch. Its remaining assumptions and conclusions must also be free of these parameters.

`SubstContext` contains named parameters and a formula body, for example parameters `[P]` and body `P a`. `instantiate` simultaneously substitutes arguments for the parameters using Lisa's named substitution. Repeated parameters use their last replacement. `fits` checks the list of argument sorts against the parameters, including arity.

`SubstRule` bundles these data with a comparison-variable list for each pair. Its `source` and `target` are the instantiated formulas, and `equation` is the conjunction required in the second premise. `valid` checks sorting and the comparison parameters; `fresh` checks the second premise's residual contexts. Parameters may have any simple sort. The checker exposes these rules through both its in-memory API and binary tags 33 and 34; see [the binary format](Checker/BINARY_FORMAT.md). The old one-premise tags 24 and 25 remain explicitly rejected.

### The proof tree

`Ordered.ProofTree leq Γ Δ` includes two structural operations:

- `weakening`: add formulas to either context using ordinary subset inclusion.
- `restateWeaken`: transport a proof when the old whole-sequent formula compares below the new one. This also covers equivalent sequents; no separate `restate` constructor is needed.

The other constructors specify exact shapes of premise and conclusion contexts. For example, `leftAnd` is:

```text
Γ, a, b ⊢ Δ
──────────────
Γ, a ∧ b ⊢ Δ
```

Here commas mean finite-set insertion. Additional changes to the surrounding context must be performed by explicit structural steps.

The rule families are:

| Constructors | Role |
|---|---|
| `hypothesis`, `cut` | Identity sequent and elimination of an intermediate formula. |
| `leftAnd`, `leftOr`, `leftImp`, `leftIff`, `leftNot` | Introduce a connective on the assumption side. |
| `rightAnd`, `rightOr`, `rightImp`, `rightIff`, `rightNot` | Introduce a connective on the conclusion side. |
| `leftForall`, `rightExists` | Use a chosen individual term as an instance. |
| `leftExists`, `rightForall` | Generalize using a variable satisfying a freshness condition. |
| `rightEpsilon` | Replace a witness instance by the corresponding epsilon-choice instance. |
| `leftRefl`, `rightRefl` | Remove a reflexive equality assumption or prove a reflexive equality. |
| `leftSubst`, `rightSubst` | Replace expressions simultaneously using a second premise proving their pointwise comparisons. |
| `instSchema` | Apply a well-sorted named substitution to the entire sequent. |

The quantifier rules here explicitly require the quantified variable to have sort `ind`. The richer function and predicate sorts also occur in schematic substitution.

For a first pass, read `hypothesis`, `cut`, `leftAnd`, `rightImp`, and one quantifier rule in full. Then read the equality/substitution rules. The remaining connective rules follow the same style.

## 4. AlphaBetaEtaOrder: the alpha-beta-eta baseline

Source: [AlphaBetaEtaOrder.lean](AlphaBetaEtaOrder.lean).

`Ordered.AlphaBetaEtaProof Γ Δ` abbreviates `Ordered.ProofTree AlphaBetaEta Γ Δ`.
It has exactly the Ordered rules, with alpha-beta-eta conversion as the auxiliary
comparison relation. `AlphaBetaEta` is symmetric, so a comparison step identifies
the two encoded sequent formulas up to conversion.

The file supplies the preorder and equality/implication congruence instances.
The relation is defined independently of normalization; the Lambda package
decides it on well-sorted expressions.

This baseline replaces the former Standard calculus, which had no conversion
rule. No equivalence with that removed calculus is asserted.

## 5. Weakened: put context flexibility into each rule

Source: [Weakened.lean](Weakened.lean).

The name describes relaxed requirements on the shape of contexts. It does not mean the system proves fewer sequents. Under `ProofOrder`, the later translation proves it has exactly the same derivable sequents as `Ordered`.

`AnnotatedSequent α` stores `pre`, `post`, and an annotation `val : α`. The multi-premise rules use `AnnotatedSequent Expr` to record which principal formula belongs to each premise.

### A representative rule: leftAnd

Instead of requiring the premise to be literally `Γ,a,b ⊢ Δ`, `Weakened.leftAnd` accepts a proof of arbitrary `Γ₁ ⊢ Γ₂` and a proposed conclusion `Ω₁ ⊢ Ω₂`, provided:

1. All contexts and principal formulas are well-sorted.
2. `setLeq leq Γ₂ Ω₂`: the right-side formulas are retained up to equivalence.
3. `containedExceptEither leq Γ₁ Ω₁ a b`: only the principal formulas may disappear from the left.
4. `ordContains leq (a ∧ b) Ω₁`: the combined formula occurs on the left up to order-equivalence.

Thus a single rule can include extra weakening and replacement of a principal formula by an equivalent one. The matching predicates make explicit which changes are permitted.

### Other differences from Ordered

- `hypothesis` accepts contexts containing equivalent occurrences of a formula on both sides.
- `cut` checks preservation of the surrounding formulas and permits removal of the cut formula up to equivalence.
- `leftOr` and `rightAnd` accept a nonempty **list** of annotated premises. They build left-associated disjunctions or conjunctions, rather than requiring a binary tree in the input.
- The quantifier rules preserve the same witness/freshness distinction; the eigenvariable conditions refer to the proposed conclusion.
- `leftRefl` and `rightRefl` accept terms `s,t` with `isSame leq s t`, rather than requiring literally `t,t`.
- Substitution rules check retention and introduction of formulas using the context predicates.
- `instSchema` permits memberwise order-equivalent inclusion after instantiation.
- `restateTrue` introduces a sequent whose entire formula is order-equivalent to `top`.

The last rule is a convenience of this presentation. `OrderedWeakened` derives it directly from `Ordered.rightTrue` and restatement, without assumptions on the relation. Both systems also have an explicit `leftFalse` rule.

`Weakened.ProofTree` itself requests only the relation. The laws needed to justify its equivalence with `Ordered` are requested by the translation, not by the datatype definition.

## 6. OrderedComparison: compare two Ordered instances

Source: [OrderedComparison.lean](OrderedComparison.lean).

`Ordered.Admissible source target` asks only for two-formula derivations:

```lean
∀ a b, isFormula a → isFormula b → source a b → ProofTree target {a} {b}
```

`Ordered.translate` recursively copies logical rules. For a comparison step,
it packs the premise into its formula `A`, uses admissibility to obtain `A ⊢ B`,
cuts, and unpacks `B` into the conclusion. `OrderedEncoding.lean` proves the
packing and unpacking operations using logical rules, cut, and structural
weakening, including empty contexts. No congruence or preorder is required.
The translation is noncomputable because finite-set encodings choose list enumerations.

`Ordered.provable_iff` proves equivalence of the two instances under mutual
admissibility. If `source` is included in `target`, `mapOrder` directly translates
its comparison steps; this does not require two-formula admissibility.
Then `provable_iff_of_simulation` needs only reverse two-formula admissibility.

For the checker's `ProofRelation`, `of_alphaBetaEta` embeds conversion and
`admissible` supplies the reverse two-formula derivations. Both are proved in
[Checker/ProofRelation.lean](Checker/ProofRelation.lean). This completes the
translation to the αβη baseline.

## 7. OrderedWeakened: expand flexible rules into explicit derivations

Source: [OrderedWeakened.lean](OrderedWeakened.lean).

This is the largest file in the group because it handles each constructor in both directions, including all context and sorting evidence.

### Ordered to Weakened

```lean
orderedToWeakened
```

requires only reflexivity. An exact rule application satisfies the flexible rule's checks: a retained formula matches itself, and a principal formula is equivalent to itself. Binary `leftOr` and `rightAnd` become two-element lists of premises.

### Weakened to Ordered

```lean
weakenedToOrdered
```

requires only `[Std.Refl leq]` and `[RelationCongruence leq]`. Transitivity is not needed. Its recurring construction is:

1. Translate the premise derivations recursively.
2. Weaken their contexts into the exact shape required by an Ordered rule.
3. Apply that rule.
4. Weaken its conclusion into the requested context.

For `leftAnd`, this means turning the premise into:

```text
Ω₁, a, b ⊢ Ω₂
```

then using the strict rule to obtain `Ω₁,a ∧ b ⊢ Ω₂`, and finally matching `a ∧ b` with its equivalent occurrence already present in `Ω₁`.

The required assumptions have these jobs:

| Law | Use in the translation |
|---|---|
| Reflexivity | Preserve unchanged formulas. |
| `RelationCongruence.imp_congr` | Derive a matched hypothesis by restatement; cut then replaces context members. |
| `RelationCongruence.eq_congr` | Justify the generalized reflexivity rules involving equivalent terms `s,t`. |

The helper section follows these needs. `sameHypothesis` derives a matched hypothesis by restatement. `clearLeft` and `clearRight` use cuts to replace context members; the private `replaceContexts` combines them with ordinary structural weakening. This proof-producing translation uses classical choice to select witnesses from matching propositions. The executable checker does not run this translation. `foldLeftOrOrdered` and `foldRightAndOrdered` expand nonempty premise lists into repeated binary rules. `restateTrueOrdered` derives the convenience truth rule. Basic sorting lemmas are shared with `OrderedEncoding` through [Sorting.lean](Sorting.lean).

The final theorem, `ordered_eq_weakened`, states:

```text
Nonempty (Ordered.ProofTree leq Γ Δ)
  ↔ Nonempty (Weakened.ProofTree leq Γ Δ)
```

under reflexivity and `RelationCongruence leq`. This establishes equivalence of these two presentations for that relation. It does not remove the separate admissibility requirement for translation to the alpha-beta-eta baseline.

For reading the proof, inspect one ordinary case (`leftAnd`), a multi-premise case (`leftOr`), an eigenvariable case (`rightForall`), and an equality case (`rightRefl`). These expose the main reasons for the supporting lemmas.

## 8. OrderSimulation: change the comparison relation

Source: [OrderSimulation.lean](OrderSimulation.lean).

The previous translations keep the same relation and change the presentation of derivations. `Subrelation source target` instead relates **two comparison relations**.

This is Lean's existing relation-inclusion predicate, requiring one implication:

```text
source p q                 → target p q
```

Every positive comparison made by the source must also be valid in the target. There is no requirement concerning reduction algorithms.

The file lifts this implication to each matching predicate:

| Theorem | Transfers |
|---|---|
| `same` | Bidirectional expression comparison. |
| `sequent` | Whole-sequent comparison. |
| `member`, `members` | Equivalent membership and inclusion. |
| `except`, `exceptEither` | The principal-formula exception checks. |

`refl` supplies the identity simulation.

There is no transfer of negative answers. A source algorithm may miss a comparison that the target accepts. Consequently, procedures that keep or discard assumptions based on failed comparisons need additional care; this file does not claim their outputs are identical.

This is the interface needed to justify a limited executable comparison against a stronger reference relation without requiring the executable relation itself to satisfy every law of `ProofOrder`.

## How the pieces fit after Lambda

Lambda normalization handles αβη conversion. `Orthologic.Expression` lowers
those canonical terms into the OL syntax, normalizes recursively, then compares
the results. `Orthologic.Cached` implements exactly the same operations with
verified memoization. Soundness is proved directly in Ordered αβη.

For the executable layer, read [the checker guide](Checker/README.md), followed
by the files below. The previous Combined and Quantified alternatives and
matching policies are preserved only in the archive.

## Part II: imported proofs and the executable checker

The previous files describe derivation trees. This part explains how to check a sequence of proof records, allow references to external results, and obtain a certificate for the result.

Read:

1. [Imported.lean](Imported.lean)
2. [ImportedWeakened.lean](ImportedWeakened.lean)
3. The [Orthologic pipeline and soundness proofs](Orthologic/REORGANIZATION_PLAN.md)
4. [Checker/ProofRelation.lean](Checker/ProofRelation.lean)
5. [Checker/Encoding.lean](Checker/Encoding.lean)
6. [Checker/Interfaces.lean](Checker/Interfaces.lean)
7. [Checker/Data.lean](Checker/Data.lean)
8. [Checker/Check.lean](Checker/Check.lean)
9. [Checker/Soundness.lean](Checker/Soundness.lean)
10. [Checker/Display.lean](Checker/Display.lean)
11. [Checker/Binary.lean](Checker/Binary.lean)

Import `Lisa.Checker` to load the whole package. `Imported` and
`ImportedWeakened` remain independent proof-system modules.

The executable tests use the cached OL functions. Their soundness is interpreted
through `ProofRelation`; the final certificate theorem combines the
Imported–Weakened and Weakened–Ordered translations with `Ordered.translate`.

The execution path goes in the opposite direction to this reading order:

```text
binary files → decoded expressions and proof steps → rule checks
                                                        │
                                                        v
                                        conclusion + assumptions + certificate
```

The central distinction is between **a checked derivation with outstanding assumed sequents** and **a closed derivation**. Checking a proof that uses an external result does not, by itself, prove that external result.

## 9. Imported: proof trees with outstanding assumptions

Source: [Imported.lean](Imported.lean).

### Assumed sequents are different from antecedent formulas

`Imported.Sequent` is a pair of finite sets of expressions. The proof type has one more index than `Weakened.ProofTree`:

```lean
Imported.ProofTree leq Γ Δ ss
```

Read this as: “a derivation of `Γ ⊢ Δ`, depending on the assumed sequents in `ss`.”

There are two levels of assumptions:

- `Γ` contains formulas on the left of the sequent being proved.
- `ss : Finset Sequent` contains entire sequents that have been used without yet supplying their proofs.

For example, a derivation of `P ⊢ Q` may depend on an imported theorem `∅ ⊢ R`. Its antecedent remains `{P}`; the imported theorem is recorded separately in `ss`.

### The assume constructor

```text
assume : a well-sorted sequent S → a derivation of S depending on {S}
```

This does not establish `S` without assumptions. It creates a proof leaf recording exactly what remains to be justified. Sorting is still checked.

Contrast this with `hypothesis`, which derives a sequent containing matching formulas on both sides and has no outstanding assumed sequents.

### The discharge constructor

Suppose:

```text
p proves S, depending on ss₁
q proves T, depending on ss₂
```

Discharging with `q` produces a derivation of `S` with dependencies:

```text
{U ∈ ss₁ | U is not equivalent to T} ∪ ss₂
```

`sameSequent` compares the encoded whole-sequent formulas in both directions. `discharged` filters out all assumptions equivalent to the justification's conclusion, rather than only assumptions literally equal to it.

For example:

```text
p proves S using {T, U}
q proves T using {V}
──────────────────────── discharge, assuming U does not also match T
result proves S using {U, V}
```

The justification's own dependencies are retained. In particular, assuming `T` and then using that same assumed proof to discharge `T` does not produce a closed theorem: its dependency on `T` is reintroduced.

### The remaining constructors

The logical rules follow `Weakened`, with dependency bookkeeping added:

`Imported` omits the redundant `restate` constructor: `weakening` already accepts the forward comparison. The checker still checks both comparisons for a `restate` instruction, then constructs a `weakening` certificate. Constructors also omit sorting assumptions for premise sequents, since their proofs already guarantee sorting; conclusion and principal-expression sorting remain explicit. The multi-premise conjunction and disjunction rules use the shared `foldFormulas` definition.

- Rules with no premises, such as `hypothesis` and `rightRefl`, have empty dependencies.
- Ordinary one-premise rules preserve their premise's dependencies.
- Two-premise rules take the union of their dependencies.
- Multi-premise rules use `premiseAssumptions`, a fold taking the union over every premise.

`Imported.Premise` annotates a sequent with both its principal expression and its dependency set. Repeated premises are allowed; because dependencies are finite sets, their assumptions are not counted multiple times.

This file specifies the proof object. It does not yet read step numbers, decode files, or implement the checker.

## 10. ImportedWeakened: replace assumptions with actual proofs

Source: [ImportedWeakened.lean](ImportedWeakened.lean).

The main construction explains why keeping track of imports is sufficient: if every remaining assumed sequent is provable, the entire derivation can be turned into a `Weakened` proof with no import mechanism.

### Sorting and resolution

`wellSorted` extracts sorting of the conclusion. `assumptionsWellSorted` proves that every recorded assumed sequent is well-sorted. These facts are useful when rebuilding structural steps during resolution.

`resolveWith` takes:

1. An `Imported.ProofTree` using a source order.
2. A `Subrelation source target` proof of relation inclusion.
3. A `Weakened` proof in the target order for each outstanding assumption.

It produces a `Weakened` proof of the original conclusion in the target order.

The recursion is straightforward for ordinary rules: resolve each premise, transfer its successful checks with the simulation, and apply the corresponding Weakened constructor. At an `assume` leaf, use the supplied proof.

The interesting case is `discharge`. If the source derivation removed an assumption because it matched the justification, resolution uses the justification's resolved proof and restates it to that assumption. Otherwise, it obtains the proof from the remaining assumptions supplied by the caller.

**It follows the source derivation's actual discharge decisions.** It does not recompute the remaining assumptions using the target relation, which might recognize additional equivalences. This is why positive order simulation is enough; preservation of negative comparison results is unnecessary.

`resolve` is the specialization where source and target orders are the same. These resolution functions are proof constructions, declared `noncomputable`; they are not the executable step checker.

### Embedding and equivalence theorems

`embed` turns any Weakened proof into an Imported proof with dependency set `∅`.

Together with resolution, this yields `empty_iff`:

```text
Nonempty (Weakened.ProofTree leq Γ Δ)
  ↔ Nonempty (Imported.ProofTree leq Γ Δ ∅)
```

Thus adding assumed sequents and discharge does not add new closed consequences relative to the same Weakened system. This theorem needs no additional laws on the relation and no reducer.

`withAssumptions_iff` generalizes the result to a prescribed finite set `ss`, assuming proofs of all its sequents and reflexivity of `leq`. In the reverse direction it must attach exactly that set of dependencies to an existing proof. The helper `assumeAll` constructs a derivation of truth carrying those dependencies; discharging an import-free proof with it attaches them.

The dependency set is therefore a recorded set of obligations, not a claim that each obligation is logically indispensable.

## 11. CheckerData: executable statements and certified results

Source: [Checker/Data.lean](Checker/Data.lean).

### Why statements use lists

```lean
structure Statement where
  pre : List Expr
  post : List Expr
```

A `Statement` preserves the order and repetitions in the input representation. Its `sequent` converts both lists to finite sets for the proof system. Its `formula` computes the whole-sequent encoding directly from the lists.

This avoids computing an arbitrary enumeration of a finite set.
`Statement.same_formula` proves equivalence between the executable encoding and
the abstract encoding for sorted inputs, using `Checker/Encoding.lean`.

`Statement.testLeq`, `testSame`, and `testTrue` produce positive tests for
whole-sequent implication, equivalence, and equivalence to truth. Only successes
are transported into the proof system; failures carry no logical conclusion.

### A successful result carries a certificate

The essential fields of `Checked leq` are:

```text
statement     : the actual checked conclusion
assumptions   : a finite set of outstanding Statements
certificate   : existence of an Imported proof of that conclusion
                with exactly those assumptions converted to sequents
```

The certificate is a `Nonempty (Imported.ProofTree …)`, hence a proposition. Lean checks its construction, and proofs are erased from compiled execution. The executable result retains the statement and dependency metadata without needing to retain the full derivation tree at runtime.

Keeping assumptions as `Statement`s allows executable comparisons during discharge. The certificate uses `assumptions.image Statement.sequent` to connect this metadata to the abstract proof datatype. Distinct list representations can map to the same finite-set sequent.

### Error cases

`CheckError` distinguishes:

| Error | Meaning |
|---|---|
| `emptyProof` | No final step exists. |
| `invalidReference` | A referenced step or external import is unavailable. |
| `illSortedConclusion` | A conclusion contains a non-formula. |
| `invalidConditions` | The checker did not establish a required condition. |
| `wrongConclusion` | Closed checking did not obtain the requested sequent. |
| `unresolvedAssumptions` | Closed checking found remaining obligations. |
| `atStep` | Attach the step index to another error. |

## 12. Checker: from linear records to certified derivations

Source: [Checker/Check.lean](Checker/Check.lean).

### Input records are not proofs yet

`Rule` is a datatype of requested rule applications. It stores premise references and expression parameters, but not proofs that the rule's conditions hold.

`Step` combines a proposed `statement` with a `rule`. `LinearProof` is an array of steps. Unlike `Imported.ProofTree`, such an array may contain invalid references, bad sorting, or invalid rule applications.

`Rule.name` and `Rule.references` expose the rule label and its references for diagnostics.

### Looking up premises

`lookup` interprets signed references as follows:

```text
 0 → first checked local step
 1 → second checked local step
-1 → first declared external import
-2 → second declared external import
```

Local references are looked up only in the array of already checked results. An input cannot use a future step or a circular reference to establish its own validity.

External statements are initially checked as `assume` steps. They are available as premises, but their sequents remain obligations whenever used.

### Testing the rule conditions

The checker uses the single αβη/OL pipeline for both formula matching and
whole-sequent comparison. Literal equality is a cheap sufficient match;
otherwise `Cached.isSame` compares normalized forms. One-way sequent weakening
uses `Cached.isImplying`.

`verify P` returns a `Test P`. Its `sound` field provides evidence for `P` only
when the Boolean is true. Compound tests handle conjunction, disjunction and
finite context membership. This avoids claiming decidability of provability.
There is no source/target matching selection or fallback backend.

### What a successful step does

For each rule, the checker:

1. Checks that the proposed conclusion consists of formulas.
2. Retrieves the required checked premises.
3. Tests the rule-specific sorting, freshness, matching, and context conditions.
4. Builds a `Checked` result whose certificate applies the corresponding Imported proof constructor.

For example, a `leftAnd` record names a premise and formulas `a,b`. Its successful branch establishes the same preservation and principal-formula conditions described in the Weakened section, then uses `Imported.ProofTree.leftAnd` with the premise certificate. Its dependencies are inherited from that premise.

An `assume` step succeeds for a well-sorted conclusion but returns that conclusion as an outstanding assumption. This is intentional: success means the record has the claimed derivation with the recorded obligations.

Discharge removes only assumptions whose equivalence to the justification's
conclusion was established by `Statement.testSame`, then unions the
justification's dependencies. Unrecognized assumptions remain recorded.
`Imported.ProofTree.weakenAssumptions` justifies retaining them even if the
semantic relation could discharge more. It also verifies that the proposed output is equivalent to the premise conclusion. The returned statement is the premise's actual statement, rather than silently replacing it with the proposed spelling.

### Checking a whole proof versus checking a closed proof

`check` prepares external imports, checks every step in sequence, and returns the actual result of the final checked step. An empty array fails. It does not require that the final result be closed or that it equal a separately requested target.

`checkClosed` adds both requirements:

```text
result.statement.sequent = target.sequent
result.assumptions = ∅
```

The conclusion test is literal equality of finite-set sequents, so list ordering and duplicates do not matter. It is not merely order-equivalence of the target and result.

The output `ClosedChecked leq target` carries a certificate for precisely that target with no assumed sequents.

### Using the certificate

`Checked.resolve` produces a Weakened derivation once proofs of all remaining
assumptions are supplied. `Checked.resolveWith` additionally allows transfer
along a `Subrelation` proof. The public `Checked.sound` theorem goes further:
given Ordered αβη proofs of the assumptions, it yields an Ordered αβη proof of
the conclusion. `ClosedChecked.sound` needs no assumptions.

`ClosedChecked.resolveWith` needs no imported proofs because its dependency set is empty. It yields a Weakened proof in the target relation.

These guarantees are relative to the specified relation. To continue to `Ordered`, use `ProofOrder` and the earlier translation. To continue to the alpha-beta-eta baseline, reverse admissibility in that Ordered instance is still required. Executable checking does not remove those obligations.

## 13. CheckerDisplay: readable failure diagnostics

Source: [Checker/Display.lean](Checker/Display.lean).

This small file renders expressions and statements for human inspection:

- Sorts use `ι`, `o`, and arrows.
- Identifiers include their numeric index when nonzero.
- Variables and constants retain their sort annotations.
- Applications and lambdas are rendered recursively.
- `Statement.display` joins the two lists around `⊢`.

This is diagnostic output, not a serialization format or an additional proof check. Binary checking uses it to show a failing step's conclusion and available premises.

## 14. Binary: decode external data and invoke the checker

Source: [Checker/Binary.lean](Checker/Binary.lean).

The binary layer turns two input streams—an expression table and proof records—into certified checker results.

### Reading primitive data

`Reader` reads bounded chunks and retains the current byte page. `DecodeM` combines access to the reader, `DecodeError`, and IO. Primitive readers decode bytes, integers, counts, strings, and sorts.

The string reader handles Java's modified UTF-8, including UTF-16 surrogate pairs. The sort parser translates the encoded sort syntax into `LSort`. The constant decoder distinguishes user constants from the fixed logical signature.

These are data-format operations. Their success alone says nothing about whether a proof step is valid.

### Shared expression table

`readTrees` builds an array of expressions. Entries represent variables, constants, lambdas, or applications. Composite entries refer to expressions already in the table.

The decoder rejects invalid tags, unavailable references, an expected variable that is not a variable, and expressions whose computed sort is `none`. Because the array is built incrementally, forward references are unavailable.

This table lets many proof steps refer to the same expression without repeating its full encoding.

### Proof records and bundles

`readStep` decodes a proposed `Step`: its statement, rule, parameters, and references. The decoded record is then passed to the checker; its conclusion and references are not trusted merely because they were decoded successfully.

`readProofRecord` reads the declared imports and step count, checks imports as assumptions, and checks each step as it arrives. It retains previously checked metadata for later references. It returns the final `Checked` result plus the declared counts in `ProofRecord`.

Thus byte reading and step processing are incremental, but the implementation still retains the shared expression table and the checked results needed for premise lookup. It is not constant-memory checking of the entire proof.

`readProof` is a wrapper returning only the checked result. `readBundle` reads named proof records, retaining their justification-name lists and counts, rejects an empty bundle, and rejects trailing bytes. `checkFiles` opens the expression and proof files and runs these readers, distinguishing tree-file and proof-file errors.

**At this layer, justification names are retained as metadata; `readBundle` does not link them to proofs and discharge the imports.** Its result is checked relative to the explicit outstanding assumptions. Neither a successful `readBundle` nor a successful `checkFiles` means every returned proof is closed.

### What is certified at the boundary?

A successful binary check returns the same kind of `Checked` value as the in-memory checker. Its Lean certificate concerns the decoded conclusion and its recorded assumptions, and is sound in `Ordered AlphaBetaEta`.

This is distinct from a separate formal specification of the external producer's file format. The certificate establishes derivability of the expressions actually decoded and checked; the decoder determines how bytes are interpreted.

## A worked dependency example

Suppose a proof declares the external sequent `T`, refers to it as `-1`, and derives `S` from it.

```text
external T → Checked(T, assumptions = {T})
                      │
                      v
logical steps → Checked(S, assumptions = {T})
```

`check` can successfully return this result. `checkClosed` rejects it because `T` remains unresolved.

There are two ways to finish:

1. Within the recorded proof, supply a derivation of `T` and discharge it. If that justification is closed and all other obligations are removed, the result is closed.
2. Outside that recorded proof, supply a Weakened derivation of `T` to `Checked.resolve` (or `resolveWith`). This constructs an import-free Weakened derivation of `S`.

That distinction is the purpose of the extra dependency index introduced by `Imported`: proof reuse remains explicit, and successful checking does not silently turn external assumptions into established theorems.
