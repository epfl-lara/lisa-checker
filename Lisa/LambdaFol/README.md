# From LambdaFOL to first-order logic

This package proves that a sequent in `Ordered AlphaBetaEta` is provable if
and only if its canonical first-order translation is provable in `PureFol`,
under the conclusion restrictions below.

**PureFol includes epsilon**, with witness selection and extensionality rules.
The result does not eliminate epsilon.

## What the theorem says

The main theorem is `ordered_iff_pureFol` in [Statements.lean](Statements.lean).
Each side of a sequent is written explicitly as `Finset Formula` (or
`Finset Expr` before passing to αβη classes). Functions named `formulaSet`
translate every formula in such a set.

For formula sets `Γ` and `Δ`, the theorem establishes:

```lean
OrderedAlphaBetaEta.Provable Γ Δ ↔
  PureFol.Provable
    (PureFolTranslation.canonicalFormulaSet Γ)
    (PureFolTranslation.canonicalFormulaSet Δ)
```

Here `OrderedAlphaBetaEta.Provable` means provability in `Ordered AlphaBetaEta`.
The hypotheses require every concluding expression to:

- Have sort `prop` (`isFSet Γ` and `isFSet Δ`).
- Use the admitted logical constants, including epsilon, and first-order
  function and predicate constants.
- Have free variables only of sort `ind` or `prop`.

The last two conditions form `FirstOrderCompatible`, defined in
[FirstOrderConclusions.lean](ToPureFol/FirstOrderConclusions.lean). They allow higher-order lambda
abstractions and applications inside the concluding expressions: normalization
removes those that cannot occur in first-order syntax. Free proposition
variables become nullary predicate symbols in PureFol.

**These restrictions apply only to the concluding sequent.** Intermediate
formulas may contain free higher-order variables. `canonicalFormulaSet` normalizes
each concluding formula and writes it using PureFol's constructors. The translation
is proved to succeed under the theorem's hypotheses.

## The proof in four systems

```text
Ordered AlphaBetaEta → LambdaFol → WithoutInstantiation → PureFol
```

| System | Definition and purpose |
| --- | --- |
| Ordered αβη | [Lisa's Ordered calculus](../Ordered.lean), instantiated with αβη-equivalence. It includes schematic instantiation and whole-sequent restatement. |
| LambdaFol | [ProofSystem.lean](ProofSystem.lean): formulas modulo αβη, with schematic instantiation but no primitive whole-sequent restatement. |
| WithoutInstantiation | [WithoutInstantiation.lean](WithoutInstantiation.lean): the same logical rules as LambdaFol, without schematic instantiation. |
| PureFol | [PureFol.lean](PureFol.lean): independent first-order term and formula syntax and a sequent calculus. |

Ordered → LambdaFol passes to equivalence classes and derives restatement using logical
rules. LambdaFol → WithoutInstantiation eliminates instantiation by pushing substitutions through proofs.
WithoutInstantiation → PureFol replaces higher-order symbols, normalizes, and translates each rule.
The converse embeds PureFol proofs into Ordered and recovers the original
concluding formulas up to αβη.

The proof systems use the project's generalized simultaneous replacement
rule. Proving that this rule survives each translation requires more work than
the paper's ordinary individual-term substitution cases. The supporting guides identify
that work explicitly.

## Reading routes

Start with [Syntax.lean](Syntax.lean) for shared formula classes, then the
three calculi: [ProofSystem.lean](ProofSystem.lean),
[WithoutInstantiation.lean](WithoutInstantiation.lean), and
[PureFol.lean](PureFol.lean). [Statements.lean](Statements.lean) collects the
final equivalences. In PureFol, you can initially skip renaming and substitution
lemmas and go straight to `ProofTree`.

Then follow the three proof stages:

1. [From Ordered](FromOrdered/README.md): pass to αβη classes and derive restatement.
   Start with `ProofTree.ofOrdered`.
2. [Eliminate instantiation](EliminateInstantiation/README.md): push substitutions
   through proofs. Start with `ProofTree.toWithoutInstantiation`, then
   `WithoutInstantiation.ProofTree.instantiate`.
3. [To PureFol](ToPureFol/README.md): replace higher-order symbols, normalize, and
   translate the inference rules. Start with `WithoutInstantiation.Provable.toPureFol`.

For a complete dependency-first inspection, use the inventory below. It is
a reference, not a requirement to read every supporting lemma before the
main argument. The folders share supporting syntax lemmas, so their files
are interleaved in this order.

## Checking the development

```sh
lake build Lisa.LambdaFol Tests.LambdaFol Tests.PureFolEpsilon
```

[The translation regressions](../../Tests/LambdaFol.lean) exercise
instantiation, higher-order intermediate formulas, and freshness collisions.
They also check that the forward proof actually follows LambdaFol → WithoutInstantiation → PureFol.
[The epsilon regressions](../../Tests/PureFolEpsilon.lean) cover the
epsilon rules. Axiom audits reject dependencies beyond `propext`,
`Classical.choice`, and `Quot.sound`.

## All files in dependency order

Every package import precedes the file that uses it. Imports from elsewhere
in Lisa or from external libraries are omitted. **Bold** identifies the main
definitions, translations, and proof results; supporting files are unbolded.

1. **[Syntax.lean](Syntax.lean)**
2. **[PureFol.lean](PureFol.lean)**
3. **[WithoutInstantiation.lean](WithoutInstantiation.lean)**
4. [ToPureFol/FormulaClasses.lean](ToPureFol/FormulaClasses.lean)
5. [EliminateInstantiation/Instantiation.lean](EliminateInstantiation/Instantiation.lean)
6. **[ProofSystem.lean](ProofSystem.lean)**
7. [ToPureFol/SymbolSubstitution.lean](ToPureFol/SymbolSubstitution.lean)
8. [EliminateInstantiation/InstantiationComposition.lean](EliminateInstantiation/InstantiationComposition.lean)
9. [ToPureFol/SignatureAndVariables.lean](ToPureFol/SignatureAndVariables.lean)
10. [EliminateInstantiation/ParameterRenaming.lean](EliminateInstantiation/ParameterRenaming.lean)
11. [EliminateInstantiation/InstantiateTemplate.lean](EliminateInstantiation/InstantiateTemplate.lean)
12. [EliminateInstantiation/InstantiateRuleData.lean](EliminateInstantiation/InstantiateRuleData.lean)
13. [EliminateInstantiation/Conjunction.lean](EliminateInstantiation/Conjunction.lean)
14. [EliminateInstantiation/InstantiateReplacement.lean](EliminateInstantiation/InstantiateReplacement.lean)
15. **[EliminateInstantiation/InstantiateProof.lean](EliminateInstantiation/InstantiateProof.lean)**
16. **[EliminateInstantiation/Equivalence.lean](EliminateInstantiation/Equivalence.lean)**
17. [ToPureFol/NormalizationScope.lean](ToPureFol/NormalizationScope.lean)
18. **[ToPureFol/FirstOrderShape.lean](ToPureFol/FirstOrderShape.lean)**
19. **[ToPureFol/PureFolTranslation.lean](ToPureFol/PureFolTranslation.lean)**
20. **[ToPureFol/FirstOrderExpressions.lean](ToPureFol/FirstOrderExpressions.lean)**
21. [ToPureFol/FirstOrderSubstitution.lean](ToPureFol/FirstOrderSubstitution.lean)
22. [ToPureFol/PureFolSubstitution.lean](ToPureFol/PureFolSubstitution.lean)
23. [ToPureFol/PureFolTranslationSubstitution.lean](ToPureFol/PureFolTranslationSubstitution.lean)
24. [ToPureFol/ScopedSubstitution.lean](ToPureFol/ScopedSubstitution.lean)
25. [ToPureFol/Binders.lean](ToPureFol/Binders.lean)
26. **[ToPureFol/TranslateNamedExpressions.lean](ToPureFol/TranslateNamedExpressions.lean)**
27. **[ToPureFol/DefaultAssignment.lean](ToPureFol/DefaultAssignment.lean)**
28. [ToPureFol/PureFolDerivedRules.lean](ToPureFol/PureFolDerivedRules.lean)
29. [ToPureFol/RelatedExpressions.lean](ToPureFol/RelatedExpressions.lean)
30. [ToPureFol/ReplacementRule.lean](ToPureFol/ReplacementRule.lean)
31. **[ToPureFol/TranslateProof.lean](ToPureFol/TranslateProof.lean)**
32. [ToPureFol/PureFolToOrdered/Embedding.lean](ToPureFol/PureFolToOrdered/Embedding.lean)
33. [ToPureFol/PureFolToOrdered/Roundtrip.lean](ToPureFol/PureFolToOrdered/Roundtrip.lean)
34. [ToPureFol/PureFolToOrdered/NamedExpressions.lean](ToPureFol/PureFolToOrdered/NamedExpressions.lean)
35. **[ToPureFol/PureFolToOrdered/TranslateProof.lean](ToPureFol/PureFolToOrdered/TranslateProof.lean)**
36. **[ToPureFol/FirstOrderConclusions.lean](ToPureFol/FirstOrderConclusions.lean)**
37. **[ToPureFol/PureFolToOrdered/Equivalence.lean](ToPureFol/PureFolToOrdered/Equivalence.lean)**
38. [FromOrdered/SequentEncoding.lean](FromOrdered/SequentEncoding.lean)
39. **[FromOrdered/TranslateProof.lean](FromOrdered/TranslateProof.lean)**
40. **[ToPureFol/Equivalence.lean](ToPureFol/Equivalence.lean)**
41. **[ToPureFol/FromOrdered.lean](ToPureFol/FromOrdered.lean)**
42. **[Statements.lean](Statements.lean)**
43. **[LambdaFol.lean](../LambdaFol.lean)**

The documentation consists of this overview, the
[Ordered translation guide](FromOrdered/README.md), the
[instantiation-elimination guide](EliminateInstantiation/README.md), and the
[WithoutInstantiation-to-PureFol guide](ToPureFol/README.md).
