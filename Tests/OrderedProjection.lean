import Lisa.Combined.OrderedProjection
import Lisa.Checker

open Lisa Expr Orthologic Imported.Checker

namespace Lisa.Tests.OrderedProjection

private def a : Expr := .const (.named "A" prop)
private def b : Expr := .const (.named "B" prop)
private def c : Expr := .const (.named "C" prop)

/-- Use a small synthetic atomic preorder, independently of the reference calculus. -/
private def atoms (p : Expr) : Nnf Nat :=
  .lit (if p = a then 0 else if p = b then 1 else 2) false

private abbrev leq := Orthologic.OrderedProjection.leq (· ≤ · : Nat → Nat → Prop) atoms

private def check (p q : Expr) :=
  Orthologic.OrderedProjection.check (· ≤ · : Nat → Nat → Prop) atoms p q

#guard check a b
#guard !check b a
#guard check (neg b) (neg a)
#guard !check (neg a) (neg b)
#guard check (and a (neg b)) bot
#guard check top (or (neg a) b)
#guard check (and c a) (and c b)
#guard !check (and c b) (and c a)
#guard check (or a c) (or b c)
#guard check (and a (or b c)) a
#guard check a (or a b)

-- These elaborate without an OrderAlgebra instance for the expression relation.
example : IsPreorder Expr leq := inferInstance
example : SequentEncoding leq := inferInstance
example : SequentWeakening leq := inferInstance
example : SequentTruth leq := inferInstance
example : OrderReduction leq := inferInstance
example : DecidableRel leq := inferInstance

example (proof : LinearProof) (target : Statement) :
    Except CheckError (ClosedChecked leq target) := checkClosed proof target

#eval show IO Unit from do
  let samples : List Statement :=
    [⟨[], []⟩, ⟨[], [top]⟩, ⟨[], [a, b, a]⟩, ⟨[], [b, a]⟩,
      ⟨[a, b, a], [a, b]⟩, ⟨[b, a], [b, a, a]⟩, ⟨[a, a], []⟩, ⟨[a], []⟩]
  for s in samples do
    for t in samples do
      letI := Statement.decideLeq (leq := leq) s t
      unless decide (sequentLeq leq s.sequent.1 s.sequent.2 t.sequent.1 t.sequent.2) =
          check s.formula t.formula do
        throw (IO.userError "ordered-atom encoding changed a comparison")
  let proof : LinearProof := #[
    ⟨⟨[a, b, a], [a, b]⟩, .assume⟩,
    ⟨⟨[b, a], [b, a, a]⟩, .hypothesis a⟩,
    ⟨⟨[a, b], [a, b]⟩, .discharge 0 1⟩]
  match checkClosed (leq := leq) proof ⟨[b, a], [b, a]⟩ with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"ordered-atom discharge failed: {repr e}")

-- Extending a locally monotone valuation preserves every recorded value.
example {L : Type} [Ortholattice L] (v : Nat → L)
    (hv : Constraints.Valid [0, 2, 4] (· ≤ ·) v) :
    AtomicOrder.extend [0, 2, 4] (· ≤ ·) v 2 = v 2 :=
  AtomicOrder.extend_eq _ _ v hv (by simp)

#print axioms AtomicOrder.check_valid
#print axioms Orthologic.OrderedProjection.leq_iff
#print axioms Orthologic.OrderedProjection.sound

end Lisa.Tests.OrderedProjection
