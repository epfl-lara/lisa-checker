# A to Pure: reading the proof

The paper's argument is: replace the higher-order symbols that occur inside an
A proof by suitable expressions, normalize every formula, and obtain a Pure
proof. The concluding sequent is unchanged by the replacements because it has
no free higher-order variables.

Start with [Equivalence.lean](Equivalence.lean). Its forward theorem applies
`A.toPure` with one particular replacement, `Assignment.grounding`. Its converse
reuses Pure → Ordered → B → A.

Then read [Derivation.lean](Derivation.lean). This is the induction on the A
proof. Each case applies the corresponding Pure rule. The propositional cases
are direct; the quantifier cases choose a fresh individual variable; the
replacement cases use the compatibility theorem described below.

## The forward argument

| Paper step | Where to read it |
| --- | --- |
| Choose expressions to replace the free higher-order symbols. | [Grounding.lean](Grounding.lean): `Assignment.grounding`. Individuals and propositions keep their names; higher-order variables receive constant functions. |
| Interpret the replacement on named expressions and formulas. | [Translation.lean](Translation.lean): `Assignment.expression`, `formula`, and their equations for connectives, quantifiers, and substitution. |
| Show that normalization leaves only first-order syntax. | [FirstOrderShape.lean](FirstOrderShape.lean): `InLanguage` describes the input restriction, and `normalize_formula` proves the output has first-order shape. |
| Write the normalized expression using Pure's constructors. | [Readback.lean](Readback.lean): the mutually recursive readers for terms, formulas, and argument lists; then the proof that reading succeeds. |
| Show the chosen replacement leaves the conclusion unchanged. | [Boundary.lean](Boundary.lean): `grounding_formula` and `grounding_context`. |

All of this is syntactic. `Assignment` assigns **expressions**, not semantic
values. `ScopedExpr s` is an existing typed lambda term of sort `s`, together
with proofs that its constants belong to the first-order signature and it has
no dangling bound indices. It may still contain lambda applications before
normalization.

## Why the replacement proof is substantial

A retains the project's simultaneous replacement rule, including replacement
under lambda binders. To translate that rule, it is not enough to show that
each translated expression is a formula: replacing equivalent expressions
must preserve provability, also when they occur inside applications.

[RelatedExpressions.lean](RelatedExpressions.lean) states precisely that
obligation. `Related` means provable equality at `ind`, provable equivalence at
`prop`, and preservation of related arguments at function sorts. The theorem
`fundamental` proves compatibility by induction on lambda syntax. There is no
extra proof system or semantic model here.

[ReplacementRule.lean](ReplacementRule.lean) applies that result to A's actual
replacement premise. [Binders.lean](Binders.lean) handles quantifiers and epsilon
by choosing a fresh name, applying the Pure rule to the bodies, and using eta
equivalence to recover the original functions.

`A.toPure` is stated for an arbitrary assignment fixing the admitted constants,
not only `grounding`: the induction must also work when a binder variable or a
replacement parameter is assigned a different expression.

## Supporting lemmas and the converse

These files can be consulted when a step in the main proof needs justification:

| File | Responsibility |
| --- | --- |
| [FormulaClasses.lean](FormulaClasses.lean) | A's quotient and context equations; derived individual equality substitution. |
| [Syntax.lean](Syntax.lean) | First-order symbol arities and the correspondence between lambda indices and Pure's bound slots. |
| [Normalization.lean](Normalization.lean) | Canonical shape and variable support of the existing lambda normalizer. |
| [Replacement.lean](Replacement.lean) | Simultaneous replacement of typed lambda leaves and its interaction with named syntax. |
| [FirstOrderReplacement.lean](FirstOrderReplacement.lean) | Replacement preserves scope and first-order shape and commutes with normalization in the required cases. |
| [ReadbackSubstitution.lean](ReadbackSubstitution.lean) | Reading commutes with individual substitution and binding. |
| [ScopedSubstitution.lean](ScopedSubstitution.lean) | The same facts for `ScopedExpr`; preservation of first-order function and predicate applications. |
| [PureOperations.lean](PureOperations.lean) | Binding, renaming, substitution, and free-variable lemmas for Pure syntax. |
| [PureProofs.lean](PureProofs.lean) | Short Pure derivations of congruence and equality properties. |

The converse is isolated under [Reverse/](Reverse/): `Embedding` converts Pure
syntax to typed lambda terms, `Reification` supplies named representatives,
`Roundtrip` proves that reading and embedding recover the source, and
`Derivation` translates Pure proofs to Ordered proofs. `Reverse/Equivalence`
combines those facts. The final conversion to A is in `Equivalence.lean`.

Pure includes epsilon throughout. Neither direction eliminates epsilon, uses
model-theoretic completeness, or restricts intermediate A formulas to first-order
syntax.
