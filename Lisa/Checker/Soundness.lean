import Lisa.Checker.Check

namespace Imported.Checker
open Lisa

/-- A successful check yields an actual Ordered αβη derivation once its recorded
assumptions are supplied. No completeness assumption about OL comparison is used. -/
theorem Checked.sound (result : Checked ProofRelation)
    (imports : ∀ s ∈ result.assumptions,
      Nonempty (Ordered.AlphaBetaEtaProof s.sequent.1 s.sequent.2)) :
    Nonempty (Ordered.AlphaBetaEtaProof result.statement.sequent.1 result.statement.sequent.2) := by
  have resolved := result.resolve (fun s hs => by
    obtain ⟨p⟩ := imports s hs
    exact ⟨orderedToWeakened (Ordered.mapOrder ProofRelation.of_alphaBetaEta p)⟩)
  obtain ⟨p⟩ := resolved
  exact ⟨Ordered.translate ProofRelation.admissible (weakenedToOrdered p)⟩

/-- A closed checked certificate needs no additional logical assumptions. -/
theorem ClosedChecked.sound {statement : Statement}
    (result : ClosedChecked ProofRelation statement) :
    Nonempty (Ordered.AlphaBetaEtaProof statement.sequent.1 statement.sequent.2) := by
  obtain ⟨p⟩ := result.resolveWith (fun h => h)
  exact ⟨Ordered.translate ProofRelation.admissible (weakenedToOrdered p)⟩

end Imported.Checker
