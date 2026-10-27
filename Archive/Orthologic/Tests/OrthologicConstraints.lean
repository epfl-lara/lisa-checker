import Lisa.Orthologic.Reference.Decision
import Lisa.Orthologic.Constraints
import Tests.OrthologicModel

open Lisa.Orthologic

namespace OrthologicConstraintsTests

def a : Nnf Nat := .lit 0 false
def b : Nnf Nat := .lit 1 false
def c : Nnf Nat := .lit 2 false

#guard Constraints.check [0, 1, 2] (· ≤ ·) a b
#guard Constraints.check [0, 1, 2] (· ≤ ·) a c
#guard !(Constraints.check [0, 1, 2] (· ≤ ·) b a)
#guard Constraints.check [0, 1, 2] (· ≤ ·) (.meet a b.compl) .bot
#guard Constraints.check [0, 1, 2] (· ≤ ·) (.meet a c.compl) .bot
#guard Constraints.check [0, 1, 2] (· ≤ ·) .top (.join a.compl c)
#guard Constraints.check [0, 1, 2] (· ≤ ·) c.compl a.compl
#guard !(Constraints.check [0, 1, 2] (· ≤ ·) a.compl c.compl)

-- Soundness does not require transitivity: every recorded edge remains certified.
def singleEdge (a b : Nat) : Prop := a = 0 ∧ b = 1
instance : DecidableRel singleEdge := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

#guard Constraints.check [0, 1] singleEdge (.meet a b.compl) .bot
#guard !(Constraints.check [0, 1, 2] singleEdge (.meet a c.compl) .bot)

-- Independent atoms do not justify Boolean distributivity.
#guard !(Constraints.check [0, 1, 2] (· = ·)
  (.meet a (.join b c)) (.join (.meet a b) (.meet a c)))

example {α : Type} [DecidableEq α] (atoms : List α) (r : α → α → Prop)
    [DecidableRel r] (ht : ∀ {a b c}, r a b → r b c → r a c)
    (p q : Nnf α) (hp : p.All (· ∈ atoms)) (hq : q.All (· ∈ atoms)) :
    Constraints.check atoms r p q = true ↔
      ∀ (L : Type) [Ortholattice L] (v : α → L),
        Constraints.Valid atoms r v → p.eval v ≤ q.eval v :=
  Constraints.check_valid atoms r ht p q hp hq

-- Empty support is valid for formulas without atoms.
#guard Constraints.check ([] : List Nat) (· ≤ ·) .bot .top
#guard !(Constraints.check ([] : List Nat) (· ≤ ·) .top .bot)

example {α : Type} [DecidableEq α] [Hashable α] (atoms : List α)
    (r : α → α → Prop) [DecidableRel r] (p q : Nnf α) :
    Calculus.Reference.decideLe (p.bind (Constraints.encode atoms r))
      (q.bind (Constraints.encode atoms r)) = Constraints.check atoms r p q :=
  Calculus.Reference.decideLe_eq _ _

#print axioms Constraints.check_sound
#print axioms Constraints.check_complete

end OrthologicConstraintsTests
