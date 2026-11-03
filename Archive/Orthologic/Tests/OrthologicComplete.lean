import Lisa.Orthologic.Reference.Search
import Lisa.Orthologic.Reference.Decision
import Lisa.Orthologic.Substitution
import Lisa.Orthologic.Free
import Lisa.Orthologic.Certificate
import Tests.OrthologicModel

open Lisa Lisa.Orthologic
open Lisa.Orthologic.Reference

namespace OrthologicCompleteTests

open Calculus

def a : Nnf Nat := .lit 0 false
def b : Nnf Nat := .lit 1 false
def c : Nnf Nat := .lit 2 false

#guard decideLe a a
#guard decideLe (.meet a b) a
#guard decideLe a (.join a b)
#guard decideLe a (.meet a (.join a b))
#guard decideLe (.meet a a.compl) .bot
#guard decideLe .top (.join a a.compl)
#guard decideLe (.meet (.join a b) (.meet a.compl b.compl)) .bot
#guard decideLe (.join (.meet a b) (.join a.compl b.compl)) .top
#guard !(decideLe a b)
#guard !(decideLe (α := Nat) .top .bot)
#guard !(decideLe (.meet a (.join b c)) (.join (.meet a b) (.meet a c)))
#guard !(decideLe a (.join (.meet a b) (.meet a b.compl)))

#guard (value (.meet a .top) : Free Nat) = value a
#guard (value (.meet a b) : Free Nat) ≤ value a
#guard !decide ((value a : Free Nat) ≤ value b)
#guard !decide ((value a : Free Nat) = value b)

-- Compare the fast recognizer against the complete procedure on small formulas.
def small : List (Nnf Nat) :=
  [.bot, .top, a, a.compl, b, .meet a b, .join a b,
    .meet a a.compl, .join a a.compl]

#eval show IO Unit from do
  for p in small do
    for q in small do
      unless checkLe p q == Calculus.Reference.decideLe p q do
        throw (IO.userError s!"Search disagrees with complete saturation: {repr p}, {repr q}")
      unless decideLe p q == Calculus.Reference.decideLe p q do
        throw (IO.userError "Complete fast path disagrees with saturation")

-- No hash instance is required for the completeness baseline.
structure Atom where
  index : Nat
  deriving DecidableEq

#guard decideLe (.meet (.lit (Atom.mk 0) false) (.lit (Atom.mk 1) false))
  (.lit (Atom.mk 0) false)
#guard !(decideLe (.lit (Atom.mk 0) false) (.lit (Atom.mk 1) false))

-- The decision instance proves genuine negative answers, not search failure.
example {α : Type} [DecidableEq α] (p q : Nnf α) :
    Decidable (Calculus.Derives p q) := inferInstance

example {α : Type} [DecidableEq α] (p q : Nnf α) :
    Decidable (Orthogonal p q) := inferInstance

example {α : Type} (p q : Nnf α) : Orthogonal p q ↔
    ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ (q.eval v)ᶜ :=
  Orthogonal.iff_valid p q

example : ¬ Calculus.Derives OrthologicModel.lhs OrthologicModel.rhs := by
  intro h
  exact OrthologicModel.not_distributive (h.sound OrthologicModel.valuation)

example {α : Type} [DecidableEq α] (p q : Nnf α) :
    decideLe p q = true ↔
      ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ q.eval v :=
  decideLe_valid p q

-- Exercise cut elimination at compound formulas and contraction on both sides.
example {α : Type} (p q r : Nnf α)
    (h : Proof false (some p) (some q))
    (k : Proof false (some q.compl) (some r)) :
    Nonempty (Proof false (some p) (some r)) := eliminateCut q h k

example {α : Type} (p : Nnf α) (h : Proof true (some p) none) :
    Nonempty (Proof false (some p) none) := cutFree h

-- Substitute compound formulas, including through a negative occurrence.
#guard decideLe (a.bind (fun _ => .meet b c)) (.meet b c)
#guard decideLe (a.compl.bind (fun _ => .meet b c)) (.join b.compl c.compl)

example {α β : Type} {p q : Nnf α} (h : Calculus.Derives p q)
    (f : α → Nnf β) : Calculus.Derives (p.bind f) (q.bind f) := h.bind f

example {α : Type} (p : Free α) :
    Free.substitute (fun a => value (.lit a false)) p = p :=
  Free.substitute_id p

example {α β γ : Type} (f : α → Free β) (g : β → Free γ) (p : Free α) :
    Free.substitute g (Free.substitute f p) =
      Free.substitute (fun a => Free.substitute g (f a)) p :=
  Free.substitute_comp f g p

example {α : Type} [DecidableEq α] [Hashable α] (p q : Nnf α) :
    decideLe p.normalize q.normalize = decideLe p q := decideLe_normalize p q

#print axioms Calculus.complete
#print axioms eliminateCut
#print axioms cutFree
#print axioms Calculus.Reference.saturate
#print axioms decideLe_valid
#print axioms Derives.bind
#print axioms Free.substitute_comp
#print axioms Free.compare_iff
#print axioms Orthogonal.complete

end OrthologicCompleteTests
