import Lisa.Orthologic.Reference.Decision
import Lisa.Orthologic.Free
import Tests.OrthologicModel

open Lisa.Orthologic

namespace Lisa.Tests.NormalForm

private def a : Nnf Nat := .lit 0 false
private def b : Nnf Nat := .lit 1 false
private def c : Nnf Nat := .lit 2 false

-- Exercise flattening, contextual refinement, redundancy and their duals.
#guard (Nnf.meet a (.meet b c)).normalize = (Nnf.meet (.meet a b) c).normalize
#guard (Nnf.meet a (.meet b a)).normalize = Nnf.meet b a
#guard (Nnf.meet a (.join b a)).normalize = a
#guard (Nnf.join a (.meet b a)).normalize = a
#guard (Nnf.meet (.meet a b) (.join c a)).normalize = Nnf.meet b a
#guard (Nnf.meet (.join a b) (.meet a.compl b.compl)).normalize = .bot
#guard (Nnf.join (.meet a b) (.join a.compl b.compl)).normalize = .top
#guard (Nnf.meet a (.join a.compl b)).normalize ≠ (Nnf.meet a b).normalize
#guard (Nnf.meet a b).normalize.normalize = (Nnf.meet a b).normalize

#guard Nnf.checkNormalizedLe (.join (.meet a b) (.meet a c)) (.meet a (.join b c))
#guard Nnf.checkNormalizedLe (.meet a b) (.meet b a)
#guard Nnf.checkNormalizedLe (.meet (.join a b) (.meet a.compl b.compl)) c
#guard Nnf.checkNormalizedLe c (.join (.meet a b) (.join a.compl b.compl))
#guard !Nnf.checkNormalizedLe a b
#guard !Nnf.checkNormalizedLe (α := Nat) .top .bot
#guard !Nnf.checkNormalizedLe (.join a b) (.meet a b)
#guard !Nnf.checkNormalizedLe OrthologicModel.lhs OrthologicModel.rhs
#guard !Nnf.checkNormalizedLe a (.join (.meet a b) (.meet a b.compl))

-- Keep a negative, wide meet/join comparison from enumerating interleavings.
private def distinctMeet (n : Nat) : Nnf Nat :=
  (List.range n).foldr (fun i p => .meet (.lit i false) p) .top

private def distinctJoin (n : Nat) : Nnf Nat :=
  (List.range n).foldr (fun i p => .join (.lit (n + i) false) p) .bot

#guard !Nnf.structuralLe (distinctMeet 64) (distinctJoin 64)

-- Normalization and structural containment require no atom hash instance.
private structure Atom where
  index : Nat
  deriving DecidableEq

#guard Nnf.checkNormalizedLe
  (.meet (.lit (Atom.mk 0) false) (.join (.lit (Atom.mk 1) false) (.lit (Atom.mk 0) false)))
  (.lit (Atom.mk 0) false)

private def small : List (Nnf Nat) :=
  [.bot, .top, a, a.compl, b, b.compl, .meet a b, .join a b,
    .meet a a.compl, .join a a.compl, .meet a (.join b a),
    .meet (.join a b) (.meet a.compl b.compl),
    .meet a (.join b c), .join (.meet a b) (.meet a c),
    .meet (.join a b) (.join a.compl c),
    .join (.meet a b) (.meet a.compl c),
    .meet a (.join (.meet a b) (.meet a b.compl)),
    .join a (.meet (.join a b) (.join a b.compl))]

-- Compare against independent complete saturation, including negative cases.
#eval show IO Unit from do
  for p in small do
    for q in small do
      let expected := Calculus.Reference.decideLe p q
      unless Calculus.decideLe p.normalize q.normalize == expected do
        throw (IO.userError s!"Normalization changed order: {repr p}, {repr q}")
      unless Nnf.checkNormalizedLe p q == expected do
        throw (IO.userError s!"Normalized containment disagrees with saturation: {repr p}, {repr q}")
      unless Calculus.decideLe p q == expected do
        throw (IO.userError "Normalized fast path disagrees with complete saturation")

-- Check preservation at every valuation in a nondistributive ortholattice.
#eval show IO Unit from do
  let values := [OrthologicModel.Diamond.bot, .top, .a, .a', .b, .b']
  for x in values do
    for y in values do
      let v := fun n => if n = 0 then x else y
      for p in small do
        unless p.normalize.eval v == p.eval v do
          throw (IO.userError s!"Changed nondistributive interpretation: {repr p}")

example {α : Type} [DecidableEq α] (p q : Nnf α) :
    Calculus.Derives p.normalize q.normalize ↔ Calculus.Derives p q :=
  Calculus.derives_normalize_iff p q

#print axioms Nnf.structuralLe_sound
#print axioms Nnf.eval_normalize
#print axioms Nnf.checkNormalizedLe_sound
#print axioms Nnf.structuralLe_iff_lattice
#print axioms Nnf.reduced_normalize
#print axioms Nnf.checkNormalizedLe_iff
#print axioms Calculus.Reference.decideLe_eq
#print axioms Calculus.derives_normalize_iff

end Lisa.Tests.NormalForm
