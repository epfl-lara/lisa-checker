# Orders and proof systems in Lisa

This guide covers the next layer after [the Lambda package](Lambda/README.md): the interfaces for comparing expressions, three presentations of sequent proofs, and the translations between them.

The purpose of this layer is to describe **which proof steps the checker may accept and how flexible proof steps can be justified by more explicit ones**. It does not yet implement the concrete comparison algorithm or the executable checker.

## Reading order and dependencies

Read these files in this order:

1. [Orthologic/Basic.lean](Orthologic/Basic.lean): the algebraic structure used to interpret propositional operations.
2. [Order.lean](Order.lean): expression comparison, reduction, context matching, and the required laws.
3. [Ordered.lean](Ordered.lean): explicit sequent rules with order-based structural steps.
4. [Standard.lean](Standard.lean): the corresponding rules with ordinary set-inclusion weakening.
5. [Weakened.lean](Weakened.lean): rules accepting flexible premise and conclusion contexts.
6. [StandardOrdered.lean](StandardOrdered.lean): translations between Standard and Ordered, under stated assumptions.
7. [OrderedWeakened.lean](OrderedWeakened.lean): translations between Ordered and Weakened.
8. [OrderSimulation.lean](OrderSimulation.lean): transferring successful comparisons between different orders.

The local import graph is:

```text
Syntax ──────────┐
                v
Orthologic.Basic → Order → Ordered → Standard
                     │       │          │
                     │       └→ Weakened│
                     │                  │
                     │   Ordered + Standard → StandardOrdered
                     │   Ordered + Weakened → OrderedWeakened
                     └→ OrderSimulation
```

`OrderSimulation` can be read immediately after `Order`; its later position makes its purpose easier to appreciate. `Standard` imports `Ordered` to reuse the substitution data definitions, although its own proof datatype has no order parameter.

## What a sequent and a proof tree mean

The notation

```text
Γ ⊢ Δ
```

represents a sequent with assumptions `Γ` and alternatives `Δ`. Informally, if all assumptions hold, at least one formula on the right holds. Both sides are `Finset Expr`, so order and repetitions of formulas are already forgotten.

**Here `Γ` is a finite set of formulas, not the list of variable sorts used in `Lambda.Term Γ s`.** These are different uses of the same conventional letter.

The declarations

```lean
Standard.ProofTree Γ Δ
Ordered.ProofTree leq Γ Δ
Weakened.ProofTree leq Γ Δ
```

are types of derivation trees for that sequent. Their constructors are inference rules: constructing a tree requires supplying its premises and side conditions.

The trees live in `Type`. Therefore, the statement that a derivation exists is written `Nonempty (…ProofTree …)`. The equivalence theorems below compare existence of derivations, not literal equality of trees.

`Expr` is the original named syntax. It does not enforce sorting in its datatype, so the rules explicitly require `isFormula φ`, `isTerm t`, and `isFSet Γ` (every member of `Γ` is a formula).

## 1. Orthologic/Basic: the algebra behind the order

Source: [Orthologic/Basic.lean](Orthologic/Basic.lean).

This short file defines `Ortholattice α`. It extends a lattice with a greatest element, a least element, and a complement operation:

| Algebra | Intended propositional operation |
|---|---|
| `a ⊓ b` | conjunction |
| `a ⊔ b` | disjunction |
| `⊤`, `⊥` | truth, falsity |
| `aᶜ` | negation |

Its additional fields say that complement reverses order, applying it twice returns the original element, and `a ⊔ aᶜ = ⊤`.

There is **no distributivity assumption** in this class. Do not silently replace it with a Boolean algebra when reading proofs. Nor does this file define expressions, proofs, normalization, or a decision procedure: it only specifies an algebraic interface.

## 2. Order: comparison and the laws needed by its consumers

Source: [Order.lean](Order.lean).

### An order starts as an arbitrary relation

```lean
abbrev Order := Expr → Expr → Prop
```

Despite its name, this abbreviation alone imposes no reflexivity, transitivity, or antisymmetry. Those properties are requested separately where needed.

For a chosen relation `leq`:

```text
isSame leq p q := leq p q ∧ leq q p
```

This is comparison in both directions. It is not Lean equality, and it is not defined to be alpha-beta-eta conversion. A concrete order can recognize additional propositional relationships.

### OrderAlgebra: give comparison an algebraic interpretation

`OrderAlgebra leq` supplies an ortholattice `Carrier` and a function `eval : Expr → Carrier`, with:

```text
leq p q ↔ eval p ≤ eval q
```

The remaining fields specify the interpretation of truth, falsity, conjunction, disjunction, negation, implication, and equivalence. In particular, implication is interpreted as `eval pᶜ ⊔ eval q`.

Antisymmetry belongs to the carrier, not to expression syntax. Different expressions can have the same interpretation. The theorem `OrderAlgebra.same_iff` makes this precise:

```text
isSame leq p q ↔ eval p = eval q
```

The file derives a preorder on expressions and the sequent encoding, weakening, and truth laws from this interpretation. It does not derive a decision procedure or an expression reducer from the algebra.

### OrderReduction: a certified simplifier

`OrderReduction leq` supplies:

```text
reduce : Expr → Expr
isSame leq (reduce p) p
(reduce p).sort = p.sort
```

The interface does not require complete normalization, canonical forms, or idempotence. It only requires preservation of comparison in both directions and of the computed sort.

`reducedSame leq p q` means literal equality of `reduce p` and `reduce q`. With transitivity, `OrderReduction.sound` proves:

```text
reducedSame leq p q → isSame leq p q
```

The converse is not required. A reducer may fail to make two equivalent expressions literally equal.

Other useful results are `leq_iff` (reducing both sides preserves a comparison), `monotone`, and, under `OrderAlgebra`, `value_reduce`. The `map_and`, `map_or`, and `map_neg` theorems express compatibility up to `isSame`, not syntactic equality of the resulting expressions.

### Matching formulas and contexts

These predicates describe different strengths of matching. Their differences matter in `Weakened`:

| Predicate | Meaning |
|---|---|
| `ordContains leq p Γ` | Some member of `Γ` is order-equivalent to `p`. |
| `setLeq leq Γ Δ` | Every member of `Γ` has an order-equivalent member in `Δ`. |
| `reducedSubset leq Γ Δ` | Every member of `Γ` has a member of `Δ` with literally equal reduced syntax. |
| `containedExcept leq Γ Δ p` | Every member of `Γ` either matches a member of `Δ` by reduced equality or is order-equivalent to `p`. |
| `containedExceptEither leq Γ Δ p q` | Every member of `Γ` is literally in `Δ`, or is order-equivalent to `p` or `q`. |

In particular, `setLeq` is inclusion **up to equivalence**, not pointwise one-way inequality. And `containedExceptEither` uses literal membership for retained formulas; it is not just two copies of `containedExcept`.

Example: if the premise contains `{a, b, c}` and the conclusion retains `{c}`, then `containedExceptEither … {a,b,c} {c} a b` permits removing the two principal formulas. It would not permit silently dropping an unrelated `d`.

The lemmas at the end of the file turn ordinary subset or set-difference facts into these predicates. `setLeq_of_reducedSubset` uses the soundness of reduction and requires transitivity.

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

The finite-set encodings are `noncomputable`, because they use `Finset.toList`. `listSequentToFormula` instead works directly on the input lists. `SequentEncoding` says that either encoding gives the same comparisons, on both sides of `leq`; it accounts for permutation and duplicate removal.

Under `OrderAlgebra`, `value_sequent` identifies the interpretation as:

```text
(infimum of the antecedent interpretations)ᶜ
  ⊔ (supremum of the succedent interpretations)
```

This explains `SequentWeakening`: adding assumptions or adding alternatives makes the encoded sequent greater in the order. `SequentTruth` says every encoded sequent lies below `top`; it does not say every sequent is true or derivable.

### Which assumptions are bundled together?

| Interface | What it provides |
|---|---|
| `SequentEncoding` | Agreement of list and finite-set encodings under comparison. |
| `SequentWeakening` | Memberwise equivalent inclusion implies whole-sequent comparison. |
| `SequentTruth` | Every encoded sequent compares below `top`. |
| `TermEqualityCongruence` | Replacing individual terms by order-equivalent terms preserves equality formulas up to `isSame`. |
| `CheckerOrder` | Sequent encoding, reduction, and decidable comparison. |
| `ImportOrder` | Reduction, reflexivity, and the sequent truth bound. |
| `ProofOrder` | `ImportOrder`, a preorder, sequent weakening, and term-equality congruence. |

The `.of` definitions package separately supplied instances into these bundles.

**`ProofOrder` does not extend `CheckerOrder`.** One supplies laws for proof translations; the other supplies operations for executable checking. An executable comparison need not itself be transitive. Its positive answers can instead be justified in a stronger reference relation later.

## 3. Ordered: explicit logical rules with order-based structural steps

Source: [Ordered.lean](Ordered.lean).

### Substitution data shared by the proof systems

`SubstPair` contains a `source` and a `target` expression. `wellSorted` requires the source to be well-sorted and both computed sorts to agree.

`SubstPair.liftEq` expresses the relationship needed to substitute one expression for the other. It applies function or predicate expressions to fresh variables, compares their results, and universally quantifies those variables. Examples, schematically:

```text
s, t : ind         → s = t
P, Q : prop        → P ↔ Q
f, g : ind → ind   → ∀x. f x = g x
P, Q : ind → prop  → ∀x. P x ↔ Q x
```

This constructs a formula; it does not assert that the formula is already proved. The substitution rules put such formulas among their assumptions.

`SubstContext` contains named parameters and a formula body, for example parameters `[P]` and body `P a`. `instantiate` simultaneously substitutes arguments for the parameters using Lisa's named substitution. Repeated parameters use their last replacement. `fits` checks the list of argument sorts against the parameters, including arity. `wellSorted` checks the body and the allowed functional/predicate parameter sorts.

### The proof tree

`Ordered.ProofTree leq Γ Δ` includes two structural operations:

- `weakening`: transport a proof when the old whole-sequent formula compares below the new one.
- `restate`: transport a proof when those formulas compare in both directions.

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
| `leftSubstEq`, `rightSubstEq` | Replace expressions in a formula under the lifted equality/equivalence assumptions. |
| `instSchema` | Apply a well-sorted named substitution to the entire sequent. |

The quantifier rules here explicitly require the quantified variable to have sort `ind`. The richer function and predicate sorts also occur in schematic substitution.

For a first pass, read `hypothesis`, `cut`, `leftAnd`, `rightImp`, and one quantifier rule in full. Then read the equality/substitution rules. The remaining connective rules follow the same style.

## 4. Standard: the same logical rules with literal weakening

Source: [Standard.lean](Standard.lean).

`Standard.ProofTree Γ Δ` has no `leq` parameter. It uses the same logical, quantifier, equality, epsilon, and schema-instantiation rules, but its weakening constructor requires:

```text
Γ ⊆ Γ'    and    Δ ⊆ Δ'
```

There is no `restate` constructor. Formula identification and arbitrary whole-sequent comparisons are not built into its structural rule.

For example, extending a proof of `a ⊢ a` to `a,b ⊢ a,c` is directly available by weakening. Replacing `a` by a differently written order-equivalent expression is not justified by that constructor alone.

This file defines a proof system, not a theorem that every accepted expression comparison is admissible in that system. That distinction explains the hypothesis required in the next translation file.

## 5. Weakened: put context flexibility into each rule

Source: [Weakened.lean](Weakened.lean).

The name describes relaxed requirements on the shape of contexts. It does not mean the system proves fewer sequents. Under `ProofOrder`, the later translation proves it has exactly the same derivable sequents as `Ordered`.

`AnnotatedSequent α` stores `pre`, `post`, and an annotation `val : α`. The multi-premise rules use `AnnotatedSequent Expr` to record which principal formula belongs to each premise.

### A representative rule: leftAnd

Instead of requiring the premise to be literally `Γ,a,b ⊢ Δ`, `Weakened.leftAnd` accepts a proof of arbitrary `Γ₁ ⊢ Γ₂` and a proposed conclusion `Ω₁ ⊢ Ω₂`, provided:

1. All contexts and principal formulas are well-sorted.
2. `reducedSubset leq Γ₂ Ω₂`: the right-side formulas are retained up to reduced equality.
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

The last rule is a convenience of this presentation. `OrderedWeakened` derives it from rules already in `Ordered`, under `ProofOrder`.

`Weakened.ProofTree` itself only requests `OrderReduction` in addition to the relation. The stronger laws needed to justify its equivalence with `Ordered` are requested by the translation, not by the datatype definition.

## 6. StandardOrdered: a conditional equivalence

Source: [StandardOrdered.lean](StandardOrdered.lean).

`standardToOrdered` recursively copies a Standard derivation. The logical constructors match; the only substantive change is converting literal subset weakening to whole-sequent weakening. It needs reflexivity and `SequentWeakening`.

The reverse function, `orderedToStandard`, needs:

```lean
SequentLeqClosedByStandard leq
```

This is a function supplying a Standard derivation of the new sequent whenever there is a Standard derivation of the old one and a whole-sequent comparison between them, with the required sorting evidence.

In other words: **prove that order-based weakening is admissible in Standard before using this translation**. The function handles `Ordered.weakening` and `Ordered.restate` through this supplied proof; the remaining constructors are copied recursively.

The main theorem is:

```text
Nonempty (Standard.ProofTree Γ Δ)
  ↔ Nonempty (Ordered.ProofTree leq Γ Δ)
```

under reflexivity, `SequentWeakening`, and `SequentLeqClosedByStandard leq`.

It is not an unconditional equivalence for every ortholattice interpretation. The source explicitly notes an obstruction to assuming this automatically: Standard has no introduction rule for the literal truth constant, whereas the algebra interprets that constant as truth.

## 7. OrderedWeakened: expand flexible rules into explicit derivations

Source: [OrderedWeakened.lean](OrderedWeakened.lean).

This is the largest file in the group because it handles each constructor in both directions, including all context and sorting evidence.

### Ordered to Weakened

```lean
orderedToWeakened
```

requires reflexivity and `OrderReduction`. An exact rule application satisfies the flexible rule's checks: a retained formula matches itself, and a principal formula is equivalent to itself. Binary `leftOr` and `rightAnd` become two-element lists of premises.

### Weakened to Ordered

```lean
weakenedToOrdered
```

requires `ProofOrder`. Its recurring construction is:

1. Translate the premise derivations recursively.
2. Weaken their contexts into the exact shape required by an Ordered rule.
3. Apply that rule.
4. Weaken its conclusion into the requested context.

For `leftAnd`, this means turning the premise into:

```text
Ω₁, a, b ⊢ Ω₂
```

then using the strict rule to obtain `Ω₁,a ∧ b ⊢ Ω₂`, and finally matching `a ∧ b` with its equivalent occurrence already present in `Ω₁`.

Each part of `ProofOrder` has a concrete job:

| Law | Use in the translation |
|---|---|
| Reflexivity | Preserve unchanged formulas. |
| Transitivity and reduction preservation | Turn equal reduced forms into order-equivalence. |
| `SequentWeakening` | Convert memberwise matching into structural proof steps. |
| `SequentTruth` | Help derive `restateTrue` from the hypothesis `top ⊢ top`. |
| `TermEqualityCongruence` | Justify the generalized reflexivity rules involving equivalent terms `s,t`. |

The helper section follows these needs. It establishes context-matching facts, sorting facts, and `orderedWellSorted`; the private `weaken` combines them. `foldLeftOrOrdered` and `foldRightAndOrdered` expand nonempty premise lists into repeated binary rules. `restateTrueOrdered` derives the convenience truth rule.

The final theorem, `ordered_eq_weakened`, states:

```text
Nonempty (Ordered.ProofTree leq Γ Δ)
  ↔ Nonempty (Weakened.ProofTree leq Γ Δ)
```

under `ProofOrder leq`. This establishes equivalence of these two presentations for that order. It does not remove the separate admissibility requirement for translation to Standard.

For reading the proof, inspect one ordinary case (`leftAnd`), a multi-premise case (`leftOr`), an eigenvariable case (`rightForall`), and an equality case (`rightRefl`). These expose the main reasons for the supporting lemmas.

## 8. OrderSimulation: change the comparison relation

Source: [OrderSimulation.lean](OrderSimulation.lean).

The previous translations keep the same relation and change the presentation of derivations. `OrderSimulation source target` instead relates **two comparison relations**, each with its own reducer.

It requires two implications:

```text
source p q                 → target p q
reducedSame source p q     → reducedSame target p q
```

The first says every positive comparison made by the source is also valid in the target. The second preserves exact reduced matches used by the rules. The second is a separate requirement: target equivalence alone does not imply literal equality of the target reducer's outputs.

The file lifts these implications to each matching predicate:

| Theorem | Transfers |
|---|---|
| `same` | Bidirectional expression comparison. |
| `sequent` | Whole-sequent comparison. |
| `member`, `members` | Equivalent membership and inclusion. |
| `reducedSubset` | Inclusion using equal reduced forms. |
| `except`, `exceptEither` | The principal-formula exception checks. |

`refl` supplies the identity simulation.

There is no transfer of negative answers. A source algorithm may miss a comparison that the target accepts. Consequently, procedures that keep or discard assumptions based on failed comparisons need additional care; this file does not claim their outputs are identical.

This is the interface needed to justify a limited executable comparison against a stronger reference relation without requiring the executable relation itself to satisfy every law of `ProofOrder`.

## How the pieces fit after Lambda

Lambda normalization handles equality of expressions under alpha-beta-eta conversion. This layer describes how an expression comparison and a sort-preserving reducer can be used inside sequent proofs. It does not hard-code the Lambda normalizer into `OrderReduction`.

Later, [Combined/Lambda.lean](Combined/Lambda.lean) connects lambda normalization to an order, while the other Combined modules add further comparison and simplification capabilities.

For continuing toward executable proof checking, read [Imported.lean](Imported.lean), [ImportedWeakened.lean](ImportedWeakened.lean), [CheckerData.lean](CheckerData.lean), and [Checker.lean](Checker.lean). The interfaces and translation distinctions above are the prerequisites for understanding what their correctness statements guarantee.

## Part II: imported proofs and the executable checker

The previous files describe derivation trees. This part explains how to check a sequence of proof records, allow references to external results, and obtain a certificate for the result.

Read:

1. [Imported.lean](Imported.lean)
2. [ImportedWeakened.lean](ImportedWeakened.lean)
3. [CheckerData.lean](CheckerData.lean)
4. [Checker.lean](Checker.lean)
5. [CheckerDisplay.lean](CheckerDisplay.lean)
6. [Binary.lean](Binary.lean)

Their dependencies are:

```text
Weakened → Imported ───────────────→ CheckerData → CheckerDisplay
               │                         │              │
               v                         v              │
OrderSimulation → ImportedWeakened ───→ Checker ─────────┤
                                                       v
                                                     Binary
```

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
2. An `OrderSimulation` from that order to a target order.
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

Thus adding assumed sequents and discharge does not add new closed consequences relative to the same Weakened system. This theorem only needs the reduction interface already required by the proof datatypes; it does not need `ProofOrder`.

`withAssumptions_iff` generalizes the result to a prescribed finite set `ss`, assuming proofs of all its sequents and `ImportOrder leq`. In the reverse direction it must attach exactly that set of dependencies to an existing proof. The helper `assumeAll` constructs a derivation of truth carrying those dependencies; discharging an import-free proof with it attaches them.

The dependency set is therefore a recorded set of obligations, not a claim that each obligation is logically indispensable.

## 11. CheckerData: executable statements and certified results

Source: [CheckerData.lean](CheckerData.lean).

### Why statements use lists

```lean
structure Statement where
  pre : List Expr
  post : List Expr
```

A `Statement` preserves the order and repetitions in the input representation. Its `sequent` converts both lists to finite sets for the proof system. Its `formula` computes the whole-sequent encoding directly from the lists.

This avoids computing an arbitrary enumeration of a finite set. The `SequentEncoding` laws established earlier justify deciding abstract sequent comparisons through these executable list formulas.

`Statement.decideLeq`, `decideSame`, and `decideTrue` construct decision procedures for whole-sequent inequality, equivalence, and equivalence to truth. Each transports the decision on list formulas to the proposition about finite-set sequents.

`value_formula` gives the corresponding equality of interpretations when an `OrderAlgebra` is available.

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
| `invalidConditions` | A rule's required conditions fail. |
| `wrongConclusion` | Closed checking did not obtain the requested sequent. |
| `unresolvedAssumptions` | Closed checking found remaining obligations. |
| `atStep` | Attach the step index to another error. |

## 12. Checker: from linear records to certified derivations

Source: [Checker.lean](Checker.lean).

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

### Deciding the rule conditions

The first part of the file implements decisions for sorting and the matching predicates from `Order.lean`. Reduced context matching first tries literal inclusion and, where needed, prepares reduced contexts so that the target is not repeatedly normalized for each source formula.

These optimizations still return `Decidable` values for the specified propositions. A successful branch supplies the evidence needed by the corresponding Imported constructor.

### Matching with a cheaper relation

`Matching target` packages a source relation, its reducer and decision procedure, and an `OrderSimulation source target`.

`checkStepMatching` uses that source for rule matches and transfers successes into the target relation. Whole-sequent checks remain in the target relation. `Matching.exact` uses the target itself, with the identity simulation.

`checkStepFallback` retries using exact target matching if cheap checking returns `invalidConditions`. It does not retry arbitrary errors such as invalid references. Here “exact” means using the supplied target comparison, not completeness for all logical consequences.

The theorem `checkStepFallback_exact` proves that selecting the identity matching policy gives the same result as ordinary `checkStep`.

### What a successful step does

For each rule, the checker:

1. Checks that the proposed conclusion consists of formulas.
2. Retrieves the required checked premises.
3. Decides the rule-specific sorting, freshness, matching, and context conditions.
4. Builds a `Checked` result whose certificate applies the corresponding Imported proof constructor.

For example, a `leftAnd` record names a premise and formulas `a,b`. Its successful branch establishes the same preservation and principal-formula conditions described in the Weakened section, then uses `Imported.ProofTree.leftAnd` with the premise certificate. Its dependencies are inherited from that premise.

An `assume` step succeeds for a well-sorted conclusion but returns that conclusion as an outstanding assumption. This is intentional: success means the record has the claimed derivation with the recorded obligations.

Discharge computes the remaining assumptions by filtering against the justification's conclusion, then unions the justification's dependencies. It also verifies that the proposed output is equivalent to the premise conclusion. The returned statement is the premise's actual statement, rather than silently replacing it with the proposed spelling.

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

`Checked.resolve` produces a Weakened derivation once proofs of all remaining assumptions are supplied. `Checked.resolveWith` additionally allows transfer to a different relation using `OrderSimulation`.

`ClosedChecked.resolveWith` needs no imported proofs because its dependency set is empty. It yields a Weakened proof in the target relation.

These guarantees are relative to the specified relation. To continue to `Ordered`, use `ProofOrder` and the earlier translation. To continue to `Standard`, the separate Standard admissibility condition is still required. Executable checking does not remove those obligations.

## 13. CheckerDisplay: readable failure diagnostics

Source: [CheckerDisplay.lean](CheckerDisplay.lean).

This small file renders expressions and statements for human inspection:

- Sorts use `ι`, `o`, and arrows.
- Identifiers include their numeric index when nonzero.
- Variables and constants retain their sort annotations.
- Applications and lambdas are rendered recursively.
- `Statement.display` joins the two lists around `⊢`.

This is diagnostic output, not a serialization format or an additional proof check. Binary checking uses it to show a failing step's conclusion and available premises.

## 14. Binary: decode external data and invoke the checker

Source: [Binary.lean](Binary.lean).

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

A successful binary check returns the same kind of `Checked` value as the in-memory checker. Its Lean certificate concerns the decoded conclusion and its recorded assumptions under the chosen order.

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
