import Lisa.Orthologic.Comparison
import Lisa.Orthologic.StructuralOrder

/-! Uncached LambdaFOL OL normalization.

The organization follows the Scala checker: contextual refinement, redundancy
removal, contradiction detection, then bottom-up normalization. All recursion
terminates structurally or by the size of the expression being inspected.
-/

namespace Lisa.Orthologic
open SimpleExpr

/-- Invert a formula, cancelling an existing negation. -/
def inverse : SimpleExpr prop → SimpleExpr prop
  | .neg p => p
  | p => .neg p

/-- Flatten a factor, and refine a negative conjunction when the whole original
conjunction already implies the negation of one of its children. The negative
outer polarity uses the dual comparison, as in the Scala implementation. -/
def refineFactor (context : SimpleExpr prop) (positive : Bool)
    (p : SimpleExpr prop) (sign : Bool) : List (SimpleExpr prop) :=
  match p, sign with
  | .neg p, s => refineFactor context positive p (!s)
  | .conj ps, true => ps.attach.flatMap fun p => refineFactor context positive p.val true
  | .conj ps, false =>
      match ps.attach.find? (fun p => if positive then polarLEQ context true p.val false
        else polarLEQ p.val true context false) with
      | some p => refineFactor context positive p.val false
      | none => [.neg (.conj ps)]
  | p, s => [polar p s]
termination_by p.size
decreasing_by
  all_goals try simp only [SimpleExpr.size]
  all_goals first
    | omega
    | simpa only [SimpleExpr.size] using SimpleExpr.size_lt_conj p.property

/-- Remove a factor only when the remaining factors already imply it. -/
def pruneFactors (accepted : List (SimpleExpr prop)) :
    List (SimpleExpr prop) → List (SimpleExpr prop)
  | [] => accepted
  | p :: ps =>
      if latticesLEQ (.conj (ps ++ accepted)) p then pruneFactors accepted ps
      else pruneFactors (p :: accepted) ps

def reduceList (ps : List (SimpleExpr prop)) (positive : Bool) : List (SimpleExpr prop) :=
  let context := SimpleExpr.conj ps
  let flattened := ps.foldl (fun acc p => refineFactor context positive p true ++ acc) []
  pruneFactors [] flattened

/-- Eliminate the empty and singleton conjunction wrappers. -/
def assemble (ps : List (SimpleExpr prop)) (positive : Bool) : SimpleExpr prop :=
  let p := match ps with
    | [] => .top
    | [p] => p
    | ps => .conj ps
  if positive then p else inverse p

def checkForContradiction (ps : List (SimpleExpr prop)) (positive : Bool) : Bool :=
  if positive then ps.any (fun p => polarLEQ (.conj ps) true p false)
  else ps.any (fun p => polarLEQ p true (.conj ps) false)

def reduce (ps : List (SimpleExpr prop)) (positive : Bool) : SimpleExpr prop :=
  let qs := reduceList ps positive
  if checkForContradiction qs positive then (if positive then .neg .top else .top)
  else assemble qs positive

/-- Deterministic orientation for symmetric equalities, using a structural
comparison that retains sorts and does not allocate printed strings. -/
def orientEquality (a b : SimpleExpr ind) : SimpleExpr prop :=
  if (StructuralOrder.compareTerms a.toTerm.erase b.toTerm.erase).isLE then .equal a b else .equal b a

def normalizeEquality (a b : SimpleExpr ind) : SimpleExpr prop :=
  if latticesEQ a b then .top else orientEquality a b

def normalizeAll : SimpleExpr prop → SimpleExpr prop
  | .top => .top
  | .neg .top => .neg .top
  | p => .all p

/-- Normalize every expression sort, including formulas beneath terms and lambdas. -/
def computeNormalForm : SimpleExpr s → SimpleExpr s
  | .bound n => .bound n
  | .free x => .free x
  | .const c => .const c
  | .app f a => .app (computeNormalForm f) (computeNormalForm a)
  | .lam s b => .lam s (computeNormalForm b)
  | .top => .top
  | .conj ps => reduce (ps.attach.map fun p => computeNormalForm p.val) true
  | .neg (.conj ps) => reduce (ps.attach.map fun p => computeNormalForm p.val) false
  | .neg p => inverse (computeNormalForm p)
  | .all p => normalizeAll (computeNormalForm p)
  | .equal a b => normalizeEquality (computeNormalForm a) (computeNormalForm b)
termination_by p => p.size
decreasing_by
  all_goals try simp only [SimpleExpr.size]
  all_goals first
    | omega
    | exact size_lt_conj p.property
    | have := size_lt_conj p.property; simp only [SimpleExpr.size] at this; omega

end Lisa.Orthologic
