# Eliminating schematic instantiation

This part translates `LambdaFol.ProofTree` into
`LambdaFol.WithoutInstantiation.ProofTree`. Both use the shared formula classes
from [Syntax.lean](../Syntax.lean). See the [package overview](../README.md)
for the final theorem and its conclusion restrictions.

The essential argument is the paper's: instead of ending a proof with an
instantiation step, apply the substitution throughout the premise proof.
The implementation proves that operation valid first, then uses it to remove
all instantiation steps recursively. It does not normalize every formula
during this stage: WithoutInstantiation and LambdaFol already identify αβη-equivalent formulas.

## Start with the elimination argument

Read `ProofTree.toWithoutInstantiation` in [Equivalence.lean](Equivalence.lean). LambdaFol has WithoutInstantiation's rules plus `instSchema`.
The translation copies every ordinary rule. For instantiation, it takes the
already translated WithoutInstantiation proof and applies `WithoutInstantiation.ProofTree.instantiate` to it.
This is the only new case. `lambdaFol_iff_withoutInstantiation` combines that construction with the
immediate embedding of WithoutInstantiation into LambdaFol.

This equivalence holds for arbitrary WithoutInstantiation formula sets, including formulas with free
higher-order variables. The restriction on the concluding sequent is needed
later, for WithoutInstantiation → PureFol.

The mathematical work is in `WithoutInstantiation.ProofTree.instantiate` in
[InstantiateProof.lean](InstantiateProof.lean): **a simultaneous, sort-preserving
substitution applied to a WithoutInstantiation proof produces another WithoutInstantiation proof**. Both antecedent
and succedent are substituted. The proof is induction on the derivation; most
cases simply reapply the same rule to the substituted premises.

## Why variables sometimes need fresh names

Consider deriving `P ⊢ ∀x. P` from `P ⊢ P`, where `P` is a free proposition
variable. If we instantiate `P` by `R(x)`, keeping the binder name would give
`R(x) ⊢ ∀x. R(x)`, which is not a valid quantifier introduction.
Capture-avoiding substitution instead gives `R(x) ⊢ ∀y. R(x)`, for fresh `y`.

The quantifier cases choose such a `y` using `freshEigenvariable`. They invoke
the induction hypothesis with the old eigenvariable assigned to `y`, then
reapply the quantifier rule. Freshness ensures this override does not change
the residual formula sets. [Instantiation.lean](Instantiation.lean) supplies these
equations and the action of instantiation on αβη-equivalence classes.

## Instantiation is different from the replacement rule

Schematic instantiation replaces free variables throughout the sequent. It
needs no equality premise. The logical replacement rule instead changes a
formula using a proved equality or equivalence, possibly comparing functions
pointwise under fresh parameters.

For example, a replacement premise may compare `f(z)` and `g(z)`, with `z`
fresh for its residual assumptions. An instantiation elsewhere in that
premise can introduce `z` into an assumption. To preserve the rule, its
pointwise comparison must use a new parameter, say `w`, while the new free
`z` in the assumption stays free.

Simultaneous replacement can contain several comparisons with different
parameter lists. We therefore cannot simply instantiate their entire
conjunction with one parameter override. `instantiateComparisonPremise` in
[InstantiateReplacement.lean](InstantiateReplacement.lean) projects each
comparison, applies the appropriate override to its proof, and conjoins the
results. The original freshness assumptions justify leaving the residual
formula sets unchanged under those overrides.

The same file's `instantiateReplacement` packages the freshened rule, its
validity and freshness proofs, its source and target equations, and the rebuilt
comparison premise. The main induction then applies the left or right
replacement rule directly.

## Supporting facts, when needed

| If you want to check… | Read… |
| --- | --- |
| Why instantiation respects αβη and avoids capture under one binder | [Instantiation.lean](Instantiation.lean) |
| Why two successive instantiations agree with their composition | [InstantiationComposition.lean](InstantiationComposition.lean) |
| How lists of parameters are assigned fresh names | [ParameterRenaming.lean](ParameterRenaming.lean) |
| Why filling a formula's parameters commutes with instantiation | [InstantiateTemplate.lean](InstantiateTemplate.lean) |
| Why the transformed replacement rule has the intended source, target, and side conditions | [InstantiateRuleData.lean](InstantiateRuleData.lean) |
| How comparison conjunctions are projected and rebuilt | [Conjunction.lean](Conjunction.lean) |

A replacement template (`SubstContext`) is a formula with replacement parameters.
Assignments may repeat a parameter; the **last assignment wins**. Substitution
is simultaneous, so one image is not substituted into another.

Return to the [package file inventory](../README.md#all-files-in-dependency-order)
for a complete dependency-ordered reading route.
