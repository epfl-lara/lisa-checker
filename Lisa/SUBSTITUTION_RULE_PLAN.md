# Plan: general two-premise substitution

Replace the quantified-assumption substitution rules with two-premise rules that support expressions of any simple type. Keep simultaneous replacement and a single substitution interface throughout the proof systems and checker.

The implementation retains a list of replacements, as agreed after the initial single-replacement proposal. Successive single substitutions need not produce the same raw expression as simultaneous substitution, particularly under binders. Keeping the existing simultaneous operation avoids that conversion obligation.

This plan covers the proof rules, their correspondence proofs, and checker support. It does not implement the OL reorganization, change expression syntax, or add higher-order equality or quantifiers to the language.

**Status:** Implemented, including binary input. Following the decision to accept a breaking format change, the old checker instructions, their compatibility proofs, and the helpers used only by those proofs have been removed. Binary tags 24 and 25 are explicitly rejected. The two-premise instructions use new tags 33 and 34; their payload is specified in [Checker/BINARY_FORMAT.md](Checker/BINARY_FORMAT.md).

Validated with `lake build Lisa Tests lisa-checker`. The original stored `MGT024` export tests rejection of its retired instruction. A migrated copy supplies the comparison premise explicitly and passes all 42 steps, preserving the original conclusions and imports. The new-rule tests also run through serialization and the binary reader.

## 1. The new rules

Let `s` and `t` have the same sort

\[
\tau = \tau_1 \to \cdots \to \tau_n \to b,
\qquad b\in\{\mathrm{ind},\mathrm{prop}\}.
\]

Choose variables \(\vec x=(x_1:\tau_1,\ldots,x_n:\tau_n)\). Define the **comparison formula** by applying both expressions to all these variables:

\[
E_{\vec x}(s,t)=
\begin{cases}
s\,\vec x \equiv t\,\vec x & b=\mathrm{ind},\\
s\,\vec x \leftrightarrow t\,\vec x & b=\mathrm{prop}.
\end{cases}
\]

For each pair `(sᵢ, tᵢ)`, choose its own argument list `xsᵢ` and form `Eᵢ` as above. Let `E` be their conjunction, and let `C[s⃗]` and `C[t⃗]` mean capture-avoiding **simultaneous** substitution for the context parameters. The primitive rules are:

\[
\frac{
  \Gamma,C[\vec s]\vdash\Delta
  \qquad
  \Sigma\vdash E,\Pi
}{
  \Gamma,\Sigma,C[\vec t]\vdash\Delta,\Pi
}
\qquad
\frac{
  \Gamma\vdash C[\vec s],\Delta
  \qquad
  \Sigma\vdash E,\Pi
}{
  \Gamma,\Sigma\vdash C[\vec t],\Delta,\Pi
}.
\]

In plain text:

```text
Γ, C[s⃗] ⊢ Δ       Σ ⊢ E, Π           Γ ⊢ C[s⃗], Δ       Σ ⊢ E, Π
──────────────────────────           ──────────────────────────
Γ, Σ, C[t⃗] ⊢ Δ, Π                   Γ, Σ ⊢ C[t⃗], Δ, Π
```

An empty comparison list uses `top`; a singleton uses its comparison directly. Larger lists use the existing left-associated conjunction fold.

Their side conditions, applied to each pair, are:

- All contexts, `C`, and both instantiated results are formulas; `sᵢ` and `tᵢ` have the sort of the corresponding context parameter.
- The sorts of `vec x` are exactly the argument sorts of `τ`, in order. Both applications therefore have a ground result sort.
- The comparison variables are pairwise distinct as typed variables **within each argument list**.
- No variable in `xsᵢ` occurs free in `sᵢ`, `tᵢ`, or any formula of `Σ` or `Π`.

The last condition concerns the comparison premise's **other formulas**. It does not require the variables to be absent from the first premise or the conclusion. Keeping this distinction allows substitution in proofs with assumptions.

For a ground sort, the variable list is empty and this is ordinary equality or equivalence substitution. For a function sort, the variables may themselves have proposition or function sorts. They are free parameters of a derivation, not object-language quantified variables.

Freshness for `s` and `t`, and distinctness of the comparison variables, are essential: omitting either reproduces one of the unsound historical Scala examples recorded in the [OL plan](Orthologic/REORGANIZATION_PLAN.md#historical-two-premise-substitution-audit).

## 2. Minimal supporting definitions

Reuse `SubstPair`, `SubstContext`, `LSort.splitArgs`, `Expr.applied`, and the existing simultaneous substitution, sorting, and free-variable operations.

`SubstPair.pointwiseEq` constructs each comparison; `SubstPair.validParams` checks sorts, distinctness, and freshness for the compared expressions. `SubstRule` bundles the comparisons with their formula context. Its `source`, `target`, and `equation` compute the two instances and conjunction. `valid` checks sorting and arity; `fresh` checks the residual comparison contexts. `pointwiseEq_isFormula` and `equation_isFormula` prove that valid data produce comparison formulas.

The primitive uses `SubstContext.instantiate` unchanged, including its last-replacement behavior for repeated context parameters. It checks the formula body and parameter sorts through `SubstRule.valid`; there is no restriction to first-order function or predicate parameters.

`leftSubst` and `rightSubst` are the only constructors and checker instructions for replacement using equality or equivalence. Schematic instantiation (`instSchema`) remains a separate operation.

No new relation class, free-variable preservation axiom for `leq`, or constructor-congruence assumption is part of this change.

## 3. Ordered and the motivating example

The primitive definitions and sorting lemmas are in [Ordered.lean](Ordered.lean).

`applicationCongruence` in [Tests/OLCongruence.lean](../Tests/OLCongruence.lean) is a concrete derivation in `Ordered AlphaBetaEta` of

\[
\vdash h(\lambda x:\mathrm{prop}.\,x\land\top)
  \leftrightarrow h(\lambda x:\mathrm{prop}.\,x).
\]

It prepares the pointwise comparison using the existing logical rules and alpha-beta-eta conversion, then applies substitution. This establishes the motivating example that led to generalizing the rule.

An earlier implementation proved admissibility of the old quantified instructions. That compatibility layer was subsequently removed to simplify the maintained code. Proofs must now supply the comparison premise explicitly. The main correspondence theorem statements remain unchanged.

## 4. Propagate the rule through the proof systems

| File | Change |
| --- | --- |
| [Weakened.lean](Weakened.lean) | Replace the one-premise primitive substitution rules with versions of the new rules using the existing context-matching conventions. |
| [OrderedWeakened.lean](OrderedWeakened.lean) | Translate both premises and preserve their distinct contexts and freshness conditions. |
| [OrderedComparison.lean](OrderedComparison.lean) | Add the two-premise cases to proof translation. Both premises translate recursively; the syntactic side conditions remain unchanged. |
| [Imported.lean](Imported.lean) | Add the corresponding two-premise rules. The conclusion's imported assumptions are the union of those used by the two premises, as for cut. |
| [ImportedWeakened.lean](ImportedWeakened.lean) | Update sorting, assumption tracking, resolution of imports, and embedding proofs for the two-premise constructors. |

For the initial Weakened and Imported implementations, keep the comparison premise in the explicit form `Σ ⊢ E, Π`. Match the first premise and final contexts using the existing mechanisms. Equivalent presentations of the comparison can be prepared by existing proof steps.

This makes the freshness condition independent of order matching. In the Weakened-to-Ordered proof, the first premise can be enlarged to the required contexts; the comparison premise must retain its own `Σ` and `Π`. Apply substitution first, then adjust the conclusion. Enlarging the comparison premise to the final context could introduce a comparison variable into its assumptions and invalidate the rule.

Imported assumptions are assumed sequents that are later supplied with derivations. Resolve both premises at their existing conclusions; do not treat the imported assumption set as extra formula hypotheses in the comparison premise.

Audit every induction over these proof trees, including tests and helper definitions outside the listed files. The general relation-inclusion and proof-admissibility results should retain their existing hypotheses.

## 5. Checker and serialized proofs

In [Checker/Check.lean](Checker/Check.lean), the two-premise `leftSubst` and `rightSubst` instructions contain a `SubstRule`: the pairs, comparison variable lists, and formula context. Reference enumeration, validation, rule names, and certified proof construction handle both premises.

The checker must check sorting, full application, distinctness, and all freshness conditions. It must obtain both checked premises and combine their imported assumptions. For the explicit comparison premise, locate the comparison formula and use the remaining formulas as `Π`; do not infer freshness from equivalence under an arbitrary comparison relation.

Only the two-premise instructions remain. There are no legacy checker branches or compatibility modules.

In [Checker/Binary.lean](Checker/Binary.lean), tags **24 and 25** are rejected immediately with a specific unsupported-legacy-substitution error. They are not reinterpreted as the new rule. Tags **33 and 34** read both premise references, the replacement pairs and their comparison arguments, and the context parameters and body. Existing external exporters must emit this new layout and supply the comparison proof. Other supported tags keep their existing layouts.

Update [Checker/Display.lean](Checker/Display.lean) if its rendering requires changes. Keep the current comparison backends and Matching machinery intact during this work.

## 6. Validation

Positive tests should cover:

- Both left and right substitution, with ground equality and propositional equivalence.
- Function arguments of individual, proposition, and function sorts.
- The `h (λx. x ∧ top)` example as an actual certified derivation.
- Nonempty contexts on both premises, including a comparison variable occurring in the first premise but absent from the comparison premise's residual contexts.
- Replacement beneath a binder.
- Simultaneous substitutions, including overlapping replacements and repeated context parameters.
- Import dependencies contributed by each premise.

Negative tests reject a comparison variable free in either compared expression, repeated comparison variables, wrong sorts or arity, and a comparison variable free in either residual context of the comparison premise. They also cover a missing or incorrect comparison premise and invalid proof references. Binary tests check the explicit rejection of both retired tags, including its diagnostic.

Use [Tests/OLCongruence.lean](../Tests/OLCongruence.lean) for the motivating derivation and capture-avoidance checks, [Tests/SubstitutionRule.lean](../Tests/SubstitutionRule.lean) for parameter validation, and [Tests/SubstitutionChecker.lean](../Tests/SubstitutionChecker.lean) for executable acceptance and rejection. These modules are registered in `lakefile.toml`. Existing checker, binary, and serialized-corpus tests must continue to pass.

Build in dependency order: Ordered; Weakened and the correspondence proofs; Imported and its correspondence proofs; then the checker. Finish with `lake build`, which includes the default executable and registered tests. No `sorry` or new axioms should be used to complete the translations.

## 7. Scope and completion

The change is complete when the general rules are the only substitution interface, the old instructions and supporting compatibility code are absent, the correspondence results compile, and the tests pass.

This deliberately strengthens the calculus at higher sorts. Its intended semantic justification uses extensional function values: fresh independent parameters establish pointwise equality or equivalence under the comparison premise's assumptions. Adding a constructor and proving translations between the updated calculi does not itself formalize that semantic justification or establish conservativity over pure FOL. Those remain separate obligations for the planned conservativity development.

The Lambda package, expression representation, pure FOL calculus, and OL algorithm remain unchanged. Once this rule change is complete, the OL work can use it to justify the previously blocked higher-order replacements.
