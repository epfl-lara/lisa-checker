import Lisa.Lambda.Erasure

/-! A deterministic syntactic order for orienting individual equalities.
This order is independent of pretty printing and of logical implication.
Lexicographic comparisons stop at the first differing component. -/

namespace Lisa.Orthologic.StructuralOrder

private def compareSort : LSort → LSort → Ordering
  | .ind, .ind | .prop, .prop => .eq
  | .ind, _ => .lt
  | _, .ind => .gt
  | .prop, _ => .lt
  | _, .prop => .gt
  | .arrow a b, .arrow c d => (compareSort a c).then (compareSort b d)

private def compareId (a b : Identifier) : Ordering :=
  (compare a.name b.name).then (compare a.idx b.idx)

private def tag : Lambda.RawTerm → Nat
  | .bound .. => 0
  | .free .. => 1
  | .const .. => 2
  | .app .. => 3
  | .lam .. => 4

/-- Compare constructors, then their fields. Erasure retains all variable and
binder sorts, including the implicit argument sorts of typed applications. -/
def compareTerms : Lambda.RawTerm → Lambda.RawTerm → Ordering
  | .bound n s, .bound m t => (compareSort s t).then (compare n m)
  | .free x, .free y => (compareSort x.sort y.sort).then (compareId x.id y.id)
  | .const c, .const d => (compareSort c.sort d.sort).then (compareId c.id d.id)
  | .app f a, .app g b => (compareTerms f g).then (compareTerms a b)
  | .lam s p, .lam t q => (compareSort s t).then (compareTerms p q)
  | p, q => compare (tag p) (tag q)

end Lisa.Orthologic.StructuralOrder
