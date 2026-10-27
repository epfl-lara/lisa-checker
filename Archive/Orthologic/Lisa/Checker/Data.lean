import Lisa.Checker.Interfaces
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

namespace Statement

/-- Identify the executable fold with the abstract sequent interpretation. -/
theorem same_formula {leq : ExprRel} [Std.Refl leq] [SequentEncoding leq] (s : Statement) :
    isSame leq s.formula (sequentToFormula s.sequent.1 s.sequent.2) :=
  ⟨((SequentEncoding.compare s.pre s.post s.formula).2).mp (OrderLaws.self_le _),
    ((SequentEncoding.compare s.pre s.post s.formula).1).mp (OrderLaws.self_le _)⟩

variable {leq : ExprRel} [SequentEncoding leq]

def decideLeq [DecidableRel leq] (s t : Statement) :
    Decidable (sequentLeq leq s.sequent.1 s.sequent.2 t.sequent.1 t.sequent.2) :=
  decidable_of_iff (leq s.formula t.formula)
    (((SequentEncoding.compare s.pre s.post t.formula).1).trans
      (SequentEncoding.compare t.pre t.post
        (sequentToFormula s.sequent.1 s.sequent.2)).2)

def decideSame [DecidableRel leq] (s t : Statement) :
    Decidable (sameSequent leq s.sequent t.sequent) :=
  @instDecidableAnd _ _ (decideLeq s t) (decideLeq t s)

def decideTrue [DecidableRel leq] (s : Statement) :
    Decidable (isSame leq (sequentToFormula s.sequent.1 s.sequent.2) top) := by
  letI : Decidable (isSame leq s.formula top) := inferInstanceAs (Decidable (_ ∧ _))
  exact decidable_of_iff (isSame leq s.formula top)
    (and_congr (SequentEncoding.compare s.pre s.post top).1
      (SequentEncoding.compare s.pre s.post top).2)

end Statement

/-- Store executable metadata and an erased derivation certificate. -/
structure Checked (leq : ExprRel) where
  statement : Statement
  assumptions : Finset Statement
  certificate : Nonempty (ProofTree leq statement.sequent.1 statement.sequent.2
    (assumptions.image Statement.sequent))

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
