import Lisa.Checker.ProofRelation
import Lisa.Checker.Data
import Lisa.Checker.ProofData
import Lisa.Checker.Check
import Lisa.Checker.Soundness
import Lisa.Checker.Display
import Lisa.Checker.Binary

/-! Executable proof checking, certified results, and soundness through PureFol.
Runtime support stays in the public package; `Checker.Internal` contains erased
certificate proofs. See `Checker/README.md` for the reading order.
-/
