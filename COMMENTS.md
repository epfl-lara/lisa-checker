# Comments (from Simon)


## Ordered reading

Sort.lean
Syntax.lean
Conversion.lean (on Lisa terms)

### Lambda package (on intrinsically typed terms)
2. Lambda.Syntax
3. Lambda.Conversion
4. Lambda.Semantics
5. Lambda.Evaluation
6. Lambda.Normalization
7. Lambda.Decision
8. Lambda.Substitution
9. Lambda.Erasure
10. Lambda.Elaboration
11. Lambda.NamedEnvironment
12. Lambda.NamedAlpha
13. Lambda.NamedSubstitution
14. Lambda.NamedConversion
15. Lambda.Reification
16. Lambda.NamedReflection
17. Lambda.NamedDecision

### Expression prders and proof systems
Orthologic/Basic.lean
Order.lean
Ordered.lean
Standard.lean
Weakened.lean
StandardOrdered.lean
OrderedWeakened.lean
OrderSimulation.lean

### Imported proofs and the checker
Imported.lean
ImportedWeakened.lean
CheckerData.lean
Checker.lean
CheckerDisplay.lean
Binary.lean

### The Orthologic Package
Orthologic/Algebra.lean
Orthologic/Formula.lean
Orthologic/Calculus.lean
Orthologic/CutElimination.lean
Orthologic/Orthogonal.lean
Orthologic/Certificate.lean
Orthologic/LatticeContainment.lean
Orthologic/Structural.lean
Orthologic/Antichain.lean
Orthologic/Normalize.lean
Orthologic/Reduced.lean
Orthologic/NormalizationComplete.lean
Orthologic/Decision.lean
Orthologic/Substitution.lean
Orthologic/Free.lean
Orthologic/Constraints.lean
Orthologic/AtomicOrder.lean
Orthologic

## Notes for me

- [NamedDecision.lean](NamedDecision.lean) provides the API for the Lambda package:

```lean
compareNamed : Lisa.Expr → Lisa.Expr → Option Bool
normalizeNamed : Lisa.Expr → Option Lisa.Expr
```


## Comments

### Lambda
[`Term`](Lisa/Conversion.lean#L77) is a the type of lambda expr modulo conversion. But [`isTerm`](Lisa/Syntax.lean#L64) is a predicate on the type of lambda expr true for expressions of type `Ind`.
[`Term`](Lisa/Lambda/Syntax.lean#L13) is a type of lambda expr in de Bruijn form.

The first isn't a great name.

[`Ren`](Lisa/Lambda/Syntax.lean#L20) is not bijective in general so that's strange to me. Apparently it's not unheared of terminology in lambda calculus literature.

[`ground`](Lisa/Lambda/Semantics.lean#L18) If I understand correctly this is supposed to only take as arguments (in practice) Ind and Prop and not >>, and "ground sort" means either Ind or Prop. "ground" is confusing terminology as sorts don't contain variables, and it's weird that it can take arguments that it shouldn't.

Why have explicit contexts mapping variables instead of annotated variables? That would have entirely avoided all dependencies on Gamma everywhere?

Normalization by Evaluation is complicated enough (to me) but it seems it is quite simpler with intirinsically typed terms because then we don't need all the context/renaming machinery. LambdaV2 seems to support that? It's implemented by codex.

Also, why don't we track type intrinsically in Lisa's expressions, as we do in the actual Lisa checker? This would avoid the Elaboration machinery and make types available all the time, and guaranteed well-constructed?

I understand there are two routes to transport [`Expr`](Lisa/Syntax.lean#L7) to [`Term`](Lisa/Lambda/Syntax.lean#L13):
- `interpretNamed e (Names.free : Names [])`
- `elaborate [] (e.toNameless [])`
They are proven equivalent in NamedAlpha. Are they both necessary? Could we drop one?

### Orders
Why do we already mention Ortholattice in [Order.Lean](Lisa/Order.lean#L20)? Why is it necessary and wasn't the goal to have a version independent on the actual order as long as it is a suborder of provability? [`SequentTruth`](Lisa/Order.lean#L113) for examples is a class with a property that days that every sequent is smaller than top, that seems unnecessary?

[`Order := Expr → Expr → Prop`](Lisa/Order.lean#L8)does not imply an `Order` indeed is an order. If it was it would make a lot of the later classes theorems.

[Order.lean](Lisa/Order.lean) is a bit long and hard to understand. Maybe it's definitions could be more clearly split across which version of the system they serve? There are also a lot of classes, some that contain a single member. I think they should just be actual theorems/Definitions? 

Is the interpretation into an algebra really useful machinery? Would defining the order directly on Expr not work?

[`sequentToFormula`](Lisa/Order.lean#L89) and [`sequentLeq`](Lisa/Order.lean#L92) are `noncomputable`, which seems strange since they are supposed to be actively used?

Ordered and Weakened names are confusing because weakened is not the one that boosts the weaken rule

Why is the Ordered namespace open in the middle of the Ordered.lean file, and why is the ProofTree inside it?

Overall the package deserves a good reorganisation and tightening I think

### Imported proofs and the executable checker

Why is it built on the Weakened system (old Lisa kernel?) rather than the Ordered system (new Lisa kernel?)

There is always both the computable list-based version of sequents and the nonvomputable Finset version. Could we just use the List one? Is it simpler that way? In particular that causes a gap in the end, where the checker is weaker than the actual system, no?

In Checker.lean, why do we need the matching machinery?
Why do we have two orders, the combined and the quantified one, for the checker? That doesn't match Lisa.


### Orthologic
Why is there both Quantified and Combined? Quantified could be implemented directly.




## Comments curated from codex:

### Quantified comparison depends on an unrelated free variable's name

The comparison

```text
∀x. (P x ∧ R z) ≤ ∀x. P x
```

is accepted by `Replay.check 8` when `z` has identifier `("bound", 0)`, but rejected when its identifier is `("bound", 1)`. Both inequalities are provable in the reference relation.

`QuantifiedProjection.view` chooses a fresh variable independently for each operand. `compare` then requires the chosen binder lists to be equal. The free variable on only one side can cause those choices to differ.


###  The final soundness theorem lack end steps

`Combined.certificate_sound` produces a proof in `Weakened ExpressionOrder.leq`. There is no proof that leq is admissible, i.e. `SequentLeqClosedByStandard ExpressionOrder.leq`


### Concerns about efficiency
worth a separate analysis later