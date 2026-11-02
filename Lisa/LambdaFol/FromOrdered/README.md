# From Ordered to LambdaFOL

This part translates `Ordered.ProofTree AlphaBetaEta Γ Δ` into
`LambdaFol.ProofTree (formulaSet Γ hΓ) (formulaSet Δ hΔ)`.
The conclusion formulas become αβη-equivalence classes; their logical content
is unchanged. Schematic instantiation is retained.

Start with `ProofTree.ofOrdered` in [TranslateProof.lean](TranslateProof.lean).
The proof is induction on the Ordered derivation. Ordinary logical rules
translate directly, and αβη conversions become equality of formula classes.

Ordered's whole-sequent restatement needs a derived proof because LambdaFOL
has no primitive restatement rule. [SequentEncoding.lean](SequentEncoding.lean)
packs a sequent into its formula, identifies the source and target formula
classes, then unpacks the target sequent using logical rules and cut.

After this translation, [EliminateInstantiation](../EliminateInstantiation/README.md)
removes schematic instantiation. [ToPureFol/FromOrdered.lean](../ToPureFol/FromOrdered.lean)
composes the stages with the first-order translation.

Return to the [package overview](../README.md).
