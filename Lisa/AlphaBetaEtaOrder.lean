import Lisa.AlphaBetaEta
import Lisa.Ordered

open Lisa Expr

/-! The baseline calculus is Ordered instantiated with alpha-beta-eta conversion.
It is an instance of the same proof system, not a separate inductive calculus.
The relation itself is independent of normalization algorithms.
-/

instance : IsPreorder Expr AlphaBetaEta where
  refl := AlphaBetaEta.refl
  trans := fun _ _ _ => AlphaBetaEta.trans

instance : RelationCongruence AlphaBetaEta where
  eq_congr := by
    intro s s' t t' _ _ _ _ hs ht
    exact ⟨.app (.app (.refl _) hs.1) ht.1, .app (.app (.refl _) hs.2) ht.2⟩
  imp_congr := by
    intro p p' q q' hp hq
    exact ⟨.app (.app (.refl _) hp.1) hq.1, .app (.app (.refl _) hp.2) hq.2⟩

instance : ProofOrder AlphaBetaEta := ProofOrder.of _

/-- Lambda-FOL with alpha-beta-eta conversion as its only auxiliary relation. -/
abbrev Ordered.AlphaBetaEtaProof := Ordered.ProofTree AlphaBetaEta
