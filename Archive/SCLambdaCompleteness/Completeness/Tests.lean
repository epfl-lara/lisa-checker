import Completeness.FoundationCompleteness

namespace Lisa.SCLambdaToPure.FoundationBridge.Tests

variable {L : FirstOrder.Language.{0, 0}}

-- Roundtrip preserves equality and binding, despite the opposite indexing
-- conventions and the different representations of logical connectives.
example {M : Type} [L.Structure M] (v : Nat → M) (φ : Pure.Formula L) :
    (decode (encode φ)).Realize v default ↔ φ.Realize v :=
  (realize_decode _ v default).trans (eval_encode φ v default)

private def reflexiveSentence (L : FirstOrder.Language.{0, 0}) : L.Sentence :=
  .all (.equal (.var (.inr 0)) (.var (.inr 0)))

-- This is a Foundation proof; transport into Pure.ProofTree remains to be proved.
example : LO.Entailment.Provable (LO.FirstOrder.Theory.eqAxiom (L := language L))
    (encode (reflexiveSentence L)) := by
  apply complete_sentence
  intro M _ _
  simp [reflexiveSentence, FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.Formula.Realize, FirstOrder.Language.BoundedFormula.Realize]

/-- info: 'Lisa.SCLambdaToPure.FoundationBridge.complete_sentence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lisa.SCLambdaToPure.FoundationBridge.complete_sentence

end Lisa.SCLambdaToPure.FoundationBridge.Tests
