import Lisa.Checker.Check
import Lisa.LambdaFol.FirstOrder
import Lisa.LambdaFol.Translation
import Lisa.Checker.Internal.Soundness

namespace Imported.Checker
open Lisa

/-- A successful check yields an actual Ordered αβη derivation once its recorded
assumptions are supplied. No completeness assumption about OL comparison is used. -/
theorem Checked.sound (result : Checked ProofRelation)
    (imports : ∀ s ∈ result.assumptions,
      Nonempty (Ordered.AlphaBetaEtaProof s.sequent.1 s.sequent.2)) :
    Nonempty (Ordered.AlphaBetaEtaProof result.statement.sequent.1 result.statement.sequent.2) :=
  Internal.checked_sound result imports

/-- A closed checked certificate needs no additional logical assumptions. -/
theorem ClosedChecked.sound {statement : Statement}
    (result : ClosedChecked ProofRelation statement) :
    Nonempty (Ordered.AlphaBetaEtaProof statement.sequent.1 statement.sequent.2) :=
  Internal.closed_sound result

open LambdaFol in
/-- A closed checked certificate with a first-order conclusion yields a proof of
its canonical translation in PureFol, the first-order calculus with epsilon.
Intermediate formulas need not satisfy the first-order restrictions. -/
theorem ClosedChecked.sound_pureFol {statement : Statement}
    (result : ClosedChecked ProofRelation statement)
    (hΓ : isFSet statement.sequent.1) (hΔ : isFSet statement.sequent.2)
    (hbΓ : ∀ p ∈ statement.sequent.1, FirstOrderCompatible p)
    (hbΔ : ∀ p ∈ statement.sequent.2, FirstOrderCompatible p) :
    PureFol.Provable (PureFolTranslation.canonicalFormulaSet statement.sequent.1)
      (PureFolTranslation.canonicalFormulaSet statement.sequent.2) :=
  Internal.closed_sound_pureFol result hΓ hΔ hbΓ hbΔ

end Imported.Checker
