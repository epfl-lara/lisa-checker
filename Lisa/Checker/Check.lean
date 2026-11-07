import Lisa.Checker.Algorithm

/-! Check an entire proof, optionally requiring a closed proof of a specific sequent. -/
namespace Imported.Checker
open Lisa Expr

local notation "leq" => ProofRelation

/-- Check every record; return the actual conclusion of the final checked step. -/
def check (proof : LinearProof) (external : Array Statement := #[]) :
    Except CheckError (Checked leq) := do
  let imports ← external.mapM fun statement => checkStep #[] #[] ⟨statement, .assume⟩
  let mut checked := #[]
  for step in proof do
    match checkStep imports checked step with
    | .error e => throw (.atStep checked.size e)
    | .ok result => checked := checked.push result
  match checked.back? with
  | some result => return result
  | none => throw .emptyProof

/-- Require the requested conclusion and no remaining assumed sequents. -/
def checkClosed (proof : LinearProof) (target : Statement) (external : Array Statement := #[]) :
    Except CheckError (ClosedChecked leq target) := do
  let result ← check proof external
  if htarget : result.statement.sequent = target.sequent then
    if hempty : result.assumptions = ∅ then
      return ⟨by
        have certificate := result.certificate
        rw [hempty, Finset.image_empty] at certificate
        have hpre := congrArg Prod.fst htarget
        have hpost := congrArg Prod.snd htarget
        rw [← hpre, ← hpost]
        exact certificate⟩
    else throw .unresolvedAssumptions
  else throw .wrongConclusion

end Imported.Checker
