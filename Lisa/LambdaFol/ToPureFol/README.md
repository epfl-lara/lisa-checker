# WithoutInstantiation to PureFol: replacing symbols and normalizing the proof

The paper's argument is that higher-order symbols occurring inside a WithoutInstantiation proof
can be replaced by suitable expressions. Once every resulting formula is
normalized, the proof uses only first-order formulas. The concluding sequent
is preserved because it has no free higher-order variables.

Read `WithoutInstantiation.Provable.toPureFol` in [Equivalence.lean](Equivalence.lean) first. It combines
the general proof translation with a particular choice of replacements and
the theorem that this choice preserves the conclusion. Then read
`WithoutInstantiation.ProofTree.toPureFol` in [TranslateProof.lean](TranslateProof.lean), the induction that
translates each inference. The [package overview](../README.md) states the
precise restrictions and explains the epsilon rules.

## 1. Choose expressions for the higher-order symbols

For the final reduction, [DefaultAssignment.lean](DefaultAssignment.lean) defines
`FirstOrderAssignment.defaultAssignment`. It preserves free individual and proposition
variables and every admitted first-order or logical constant. Free variables
of function sort, and constants outside the admitted signature, receive
default expressions of the appropriate sorts.

For example, a variable of sort `ind → prop` can be replaced by `λx. ⊤`.
Defaults at function sorts ignore their arguments. At individual sort the
default is `εx. ⊤`, so no new constant needs to be added to the signature.

The proof translation is stated for more general replacements than this one.
Under binders and in replacement-rule cases, the induction must assign some
variables different expressions. These assignments are called
`FirstOrderAssignment`: **they assign syntax, not values in a semantic model**.

[FirstOrderExpressions.lean](FirstOrderExpressions.lean) defines the expressions they may assign.
`FirstOrderCompatibleExpr s` wraps a typed lambda expression of sort `s` with proofs that it
uses the admitted signature, has no free higher-order variables, and has no
dangling bound indices. It may still contain lambda abstractions and redexes.
It need not be closed: free individual and proposition names are allowed.

## 2. Show that normalization produces first-order syntax

The key distinction is between an allowed input expression and the shape of
its normal form. `FirstOrderShape.Compatible` permits higher-order bound
variables, abstractions, and applications. The grammars
`FirstOrderShape.IsTermOrFunction` and `FirstOrderShape.IsFormulaOrPredicate` describe the
first-order shapes that remain after normalization.

`normalForm_isFirstOrder` in [FirstOrderShape.lean](FirstOrderShape.lean) is the code's
counterpart of the paper's canonical-form theorem. It uses the AlphaBetaEtaNormalization
normalizer.
[NormalizationScope.lean](NormalizationScope.lean) proves the additional scope and
free-variable facts needed here.

Then [Translation.lean](../Translation.lean) writes that normal form using PureFol's own
term and formula constructors. [PureFolTranslation.lean](PureFolTranslation.lean)
proves that this operation succeeds on first-order normal forms. This step is needed because PureFol is an
independent syntax. The reading operation is partial on arbitrary inputs,
but its success is proved for the expressions admitted by the translation.

## 3. Translate the inference rules

[TranslateNamedExpressions.lean](TranslateNamedExpressions.lean) defines the action on named expressions,
the shared formula classes, and formula sets. It proves equations showing that translating
a connective gives the same connective applied to the translated formulas.
For quantifiers, it chooses a fresh target name: translating `∀x. p` gives
`∀y. p′`, where `p′` translates the body with `x` assigned to `y`.
Individual substitution and epsilon use the same translated body. The shared
predicate and binder equations are in [Binders.lean](Binders.lean).

These equations let [TranslateProof.lean](TranslateProof.lean) translate most inference
rules by directly applying the corresponding PureFol rule. `WithoutInstantiation.ProofTree.provable_toPureFol` states the
result for any symbol assignment that fixes the admitted constants. There is
no first-order restriction on the intermediate WithoutInstantiation formulas.

### Why generalized replacement needs a separate proof

The project's replacement rule can replace functions using pointwise
comparisons and can act below lambda binders. Translating the comparison
premise is not enough: we must prove that the translated expressions remain
interchangeable wherever the rule uses them.

[RelatedExpressions.lean](RelatedExpressions.lean) expresses that requirement
as `ProvablyRelated`. At individual sort it means a PureFol derivation of equality;
at proposition sort, a derivation of equivalence. At function sort, related
arguments must produce related results. These derivations retain the residual
antecedent and succedent of the comparison premise.

`apply_preserves_related` proves compatibility by induction on lambda syntax.
The supporting lemmas verify it for the admitted constants, quantifiers, and
epsilon. [ReplacementRule.lean](ReplacementRule.lean) then obtains the needed
relations from the actual simultaneous comparison premise and proves the
replacement cases of the translation.

This is the extra work required by the project's generalized replacement
rule, beyond the paper's ordinary substitution cases.

## 4. Recover the required conclusion

The general translation can change formulas containing higher-order symbols.
To obtain the desired theorem, specialize it to `defaultAssignment`.
[FirstOrderConclusions.lean](FirstOrderConclusions.lean) proves that, for each concluding formula satisfying
`FirstOrderCompatible`, this assignment gives exactly its canonical PureFol
translation. Its `defaultAssignment_formulaSet` theorem extends that fact to both sides
of the sequent.

That is the final step in `WithoutInstantiation.Provable.toPureFol`: apply the general translation,
then identify its conclusion with the required one.

## The converse

A PureFol proof is embedded into Ordered at αβη. The files under `PureFolToOrdered/`
justify both the expression conversion and the inference rules:

| Step | File |
| --- | --- |
| Express PureFol terms and formulas in typed lambda syntax | [Embedding.lean](PureFolToOrdered/Embedding.lean) |
| Give those expressions named Lisa representatives | [NamedExpressions.lean](PureFolToOrdered/NamedExpressions.lean) |
| Show that reading and embedding recover the normalized expression | [Roundtrip.lean](PureFolToOrdered/Roundtrip.lean) |
| Translate each PureFol inference into Ordered | [TranslateProof.lean](PureFolToOrdered/TranslateProof.lean) |
| Recover the original concluding sequent up to αβη | [Equivalence.lean](PureFolToOrdered/Equivalence.lean) |

For the WithoutInstantiation–PureFol equivalence, [Equivalence.lean](Equivalence.lean) composes
PureFol → Ordered → LambdaFol → WithoutInstantiation.

## Supporting facts, when needed

| If you want to check… | Read… |
| --- | --- |
| Shared equivalence classes, formula-set conversion, and freshness | [FormulaClasses.lean](FormulaClasses.lean) |
| The admitted first-order signature and translation | [FirstOrder.lean](../FirstOrder.lean), [Translation.lean](../Translation.lean) |
| Bound-variable correspondence lemmas | [SignatureAndVariables.lean](SignatureAndVariables.lean) |
| Capture-avoiding replacement on typed lambda expressions | [SymbolSubstitution.lean](SymbolSubstitution.lean) |
| Replacement's interaction with normalization and first-order shape | [FirstOrderSubstitution.lean](FirstOrderSubstitution.lean) |
| Reading commutes with individual substitution and binding | [PureFolTranslationSubstitution.lean](PureFolTranslationSubstitution.lean) |
| The corresponding substitution equations for `FirstOrderCompatibleExpr` | [ScopedSubstitution.lean](ScopedSubstitution.lean) |
| Translation of quantifiers, epsilon, and predicate application | [Binders.lean](Binders.lean) |
| Renaming, substitution, and freshness in PureFol syntax | [PureFolSubstitution.lean](PureFolSubstitution.lean) |
| Small PureFol derivations used in the compatibility proofs | [PureFolDerivedRules.lean](PureFolDerivedRules.lean) |

The complete [dependency-ordered inventory](../README.md#all-files-in-dependency-order)
lives in the package overview. Consult these supporting files when a step of
the main argument needs justification; they need not all be read first.
