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

theorem same_formula (s : Statement) (h : isFSet s.sequent.1 ∧ isFSet s.sequent.2) :
    isSame ProofRelation s.formula (sequentToFormula s.sequent.1 s.sequent.2) :=
  listSequent_same s.pre s.post h.1 h.2

/-- Executable implication supplies only a positive whole-sequent certificate. -/
def testLeq (s t : Statement) :
    Test (sequentLeq ProofRelation s.sequent.1 s.sequent.2 t.sequent.1 t.sequent.2) :=
  if hs : isFSet s.sequent.1 ∧ isFSet s.sequent.2 then
    if ht : isFSet t.sequent.1 ∧ isFSet t.sequent.2 then
      (verify (ProofRelation s.formula t.formula)).map fun h =>
        OrderLaws.transitive (s.same_formula hs).2 (OrderLaws.transitive h (t.same_formula ht).1)
    else ⟨false, by simp⟩
  else ⟨false, by simp⟩

def testSame (s t : Statement) : Test (sameSequent ProofRelation s.sequent t.sequent) :=
  if hs : isFSet s.sequent.1 ∧ isFSet s.sequent.2 then
    if ht : isFSet t.sequent.1 ∧ isFSet t.sequent.2 then
      (verify (isSame ProofRelation s.formula t.formula)).map fun h =>
        OrderLaws.same_trans (OrderLaws.same_symm (s.same_formula hs))
          (OrderLaws.same_trans h (t.same_formula ht))
    else ⟨false, by simp⟩
  else ⟨false, by simp⟩

def testTrue (s : Statement) :
    Test (isSame ProofRelation (sequentToFormula s.sequent.1 s.sequent.2) top) :=
  if hs : isFSet s.sequent.1 ∧ isFSet s.sequent.2 then
    (verify (isSame ProofRelation s.formula top)).map fun h =>
      OrderLaws.same_trans (OrderLaws.same_symm (s.same_formula hs)) h
  else ⟨false, by simp⟩

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
