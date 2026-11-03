import Lisa.Orthologic.Comparison
import Lisa.Orthologic.StructuralOrder

/-! Uncached LambdaFOL OL normalization.

The organization follows the Scala checker: contextual refinement, redundancy
removal, contradiction detection, then bottom-up normalization. All recursion
terminates structurally or by the size of the expression being inspected.
-/

namespace Lisa.Orthologic
open SimpleExpr

/-- Negate a formula, cancelling an existing negation. -/
def negate : SimpleExpr prop → SimpleExpr prop
  | .neg p => p
  | p => .neg p

/-- Simplify one factor using the original conjunction `context`.

`positive` is the polarity of the whole conjunction; `sign` is the polarity of
the current factor `p`. Descending through a negation flips only `sign`.
Positive conjunctions are flattened. A negative conjunction is replaced by the
negation of one child when `context` justifies that choice. Negative outer
polarity uses the dual comparison. `context` stays fixed throughout recursion. -/
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
  | p, s => [withPolarity p s]
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

/-- Refine factors against the original conjunction, then remove redundant ones.
Prepending each refined block fixes the order in which pruning visits them. -/
def simplifyFactors (ps : List (SimpleExpr prop)) (positive : Bool) : List (SimpleExpr prop) :=
  let context := SimpleExpr.conj ps
  let flattened := ps.foldl (fun acc p => refineFactor context positive p true ++ acc) []
  pruneFactors [] flattened

/-- Eliminate the empty and singleton conjunction wrappers. -/
def assemble (ps : List (SimpleExpr prop)) (positive : Bool) : SimpleExpr prop :=
  let p := match ps with
    | [] => .top
    | [p] => p
    | ps => .conj ps
  if positive then p else negate p

def checkForContradiction (ps : List (SimpleExpr prop)) (positive : Bool) : Bool :=
  if positive then ps.any (fun p => polarLEQ (.conj ps) true p false)
  else ps.any (fun p => polarLEQ p true (.conj ps) false)

/-- Normalize a conjunction, or its negation when `positive` is false. -/
def normalizeConjunction (ps : List (SimpleExpr prop)) (positive : Bool) : SimpleExpr prop :=
  let qs := simplifyFactors ps positive
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
  | .conj ps => normalizeConjunction (ps.attach.map fun p => computeNormalForm p.val) true
  | .neg (.conj ps) => normalizeConjunction (ps.attach.map fun p => computeNormalForm p.val) false
  | .neg p => negate (computeNormalForm p)
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
