# Comments (from Simon)


## Ordered reading

Sort.lean
Syntax.lean
AlphaBetaEta.lean (on Lisa terms)

### Lambda package (on intrinsically typed terms)
2. Lambda.Syntax
3. Lambda.AlphaBetaEta
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
14. Lambda.NamedAlphaBetaEta
15. Lambda.Reification
16. Lambda.NamedReflection
17. Lambda.NamedDecision

### Expression orders and proof systems
Order.lean
Ordered.lean
AlphaBetaEtaOrder.lean
Weakened.lean
OrderSimulation.lean
Sorting.lean
OrderedEncoding.lean
OrderedComparison.lean
OrderedWeakened.lean
Imported.lean
ImportedWeakened.lean

### The Orthologic Package
Orthologic/Syntax.lean
Orthologic/Comparison.lean
Orthologic/StructuralOrder.lean
Orthologic/Normalization.lean
Orthologic/Derivation.lean
Orthologic/Congruence.lean
Orthologic/Provability.lean
Orthologic/ComparisonSoundness.lean
Orthologic/NormalizationSoundness.lean
Orthologic/Lowering.lean
Orthologic/LoweringSoundness.lean
Orthologic/Expression.lean
Orthologic/ExpressionSoundness.lean
Orthologic/CacheKey.lean
Orthologic/Cached.lean
Orthologic/CachedSoundness.lean

### Imported proofs and the checker
Checker/ProofRelation.lean
Checker/Encoding.lean
Checker/Interfaces.lean
Checker/Data.lean
Checker/Check.lean
Checker/Soundness.lean
Checker/Display.lean
Checker/Binary.lean
CLI.lean

The previous OL/Combined/Quantified implementation is kept in
[Archive/Orthologic](Archive/Orthologic/README.md) for reference.

## Notes for me

- [NamedDecision.lean](NamedDecision.lean) provides the API for the Lambda package:

```lean
compareNamed : Lisa.Expr → Lisa.Expr → Option Bool
normalizeNamed : Lisa.Expr → Option Lisa.Expr
```


## Comments

### Lambda
[`Term`](Lisa/AlphaBetaEta.lean#L77) is a the type of lambda expr modulo conversion. But [`isTerm`](Lisa/Syntax.lean#L64) is a predicate on the type of lambda expr true for expressions of type `Ind`.
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

> **Response (SequentTruth):** I did miss that, it's indeed a bit weird. It is a result of me asking codex to minimize and isolate order preconditions. It actually found that this is one of the minimal conditions it needed to prove the correspondence between Imported and Weakened. `Lisa/ImportedWeakened.lean`

[`Order := Expr → Expr → Prop`](Lisa/Order.lean#L8)does not imply an `Order` indeed is an order. If it was it would make a lot of the later classes theorems.

> **Response:** Yes, we can change it to Rel, that's a bit stupid. We can also use `[PartialOrder leq]` in many places.

[Order.lean](Lisa/Order.lean) is a bit long and hard to understand. Maybe it's definitions could be more clearly split across which version of the system they serve? There are also a lot of classes, some that contain a single member. I think they should just be actual theorems/Definitions? 

> **Response:** Splitting and reorganization, yes, certainly. A class with one prop member is itself basically just a prop that can be carried as an instance. It's a bit neater and somewhat closer to Lean library design?

Is the interpretation into an algebra really useful machinery? Would defining the order directly on Expr not work?

> **Response:** We do define it directly on Expr? The algebra just bundles together an `Ortholattice A` and an `eval` function (the unique homomorphism into this algebra from the free ortholattice)

[`sequentToFormula`](Lisa/Order.lean#L89) and [`sequentLeq`](Lisa/Order.lean#L92) are `noncomputable`, which seems strange since they are supposed to be actively used?

> **Response:** there are list variants that are actually used for the computable parts; the reason is that Finset cannot be ordered without choice (???) as per mathlib definitions, so things become non computable. (It is defined via quotient of lists wrt permutation)
>
> I checked and `List` already implements all set operation typeclasses so it is mostly drop-in, but you just need to carry an assumption that says we are using it as a set. The Finset makes it cleaner to write and reason about, but requires a separate matching implementation.

Ordered and Weakened names are confusing because weakened is not the one that boosts the weaken rule

> **Response:** It was because Weakened weakens all the proof rules, but I am not partial to the name, I just didn't have a better idea at the time. Feel free to change it.

Why is the Ordered namespace open in the middle of the Ordered.lean file, and why is the ProofTree inside it?

> **Response — Sankalp Gambhir:** Tbh I like writing `Ordered.ProofTree` and `Weakened.ProofTree`; if you think it's bad design, you can rename it

Overall the package deserves a good reorganisation and tightening I think

### Imported proofs and the executable checker

Why is it built on the Weakened system (old Lisa kernel?) rather than the Ordered system (new Lisa kernel?)

> **Response:** Weakened is the new kernel and Ordered is the old one. Hence the chain Standard -> Ordered -> Weakened -> Imported

There is always both the computable list-based version of sequents and the nonvomputable Finset version. Could we just use the List one? Is it simpler that way? In particular that causes a gap in the end, where the checker is weaker than the actual system, no?

> **Response:** Somewhat answered above (see the response about `sequentToFormula`, `sequentLeq`, and the List/Finset representations).

In Checker/Check.lean, why do we need the matching machinery?
Why do we have two orders, the combined and the quantified one, for the checker? That doesn't match Lisa.


### Orthologic
Why is there both Quantified and Combined? Quantified could be implemented directly.

> **Response:** I have not looked carefully at the internals of the combined calculus implementation; I pushed it right after I had it working, it deserves much reorganisation.




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
