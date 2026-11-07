import Lisa.Checker.Encoding
import Lisa.Imported

open Lisa Expr

namespace Imported.Checker

/-- Retain wire order so whole-sequent formulas can be computed without choice. -/
structure Statement where
  pre : List Expr
  post : List Expr
deriving DecidableEq, Repr, Inhabited

def Statement.sequent (s : Statement) : Sequent :=
  (s.pre.toFinset, s.post.toFinset)

def Statement.formula (s : Statement) : Expr :=
  listSequentToFormula s.pre s.post


/-- Store executable metadata and an erased derivation certificate. -/
structure Checked (leq : ExprRel) where
  statement : Statement
  assumptions : Finset Statement
  certificate : Nonempty (ProofTree leq statement.sequent.1 statement.sequent.2
    (assumptions.image Statement.sequent))

/-- A checked derivation of the requested sequent with no remaining assumptions. -/
structure ClosedChecked (relation : ExprRel) (target : Statement) : Type where
  certificate : Nonempty (ProofTree relation target.sequent.1 target.sequent.2 ∅)

inductive CheckError where
  | emptyProof
  | invalidReference (reference : Int)
  | illSortedConclusion
  | invalidConditions
  | wrongConclusion
  | unresolvedAssumptions
  | atStep (index : Nat) (cause : CheckError)
deriving DecidableEq, Repr

end Imported.Checker
