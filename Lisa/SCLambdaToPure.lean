import Lisa.SCLambdaToPure.Statements

/-!
Syntactic reduction from Ordered alpha-beta-eta to an independent first-order
calculus retaining epsilon.

Read the three public entry files in order:
* `SCLambdaToPure/Pure.lean`: first-order syntax and inference rules.
* `SCLambdaToPure/A.lean`: A formula classes and inference rules.
* `SCLambdaToPure/Statements.lean`: A-Pure and Ordered-A-Pure equivalences.

Supporting proofs live in `AToPure/` and `OrderedToA/`. The latter retains B:
Ordered -> B -> A -> Pure. The first-order restriction applies only to the
concluding sequent, not to intermediate formulas. No model-theoretic completeness
or epsilon-elimination theorem is used. See `SCLambdaToPure/README.md`.
-/
