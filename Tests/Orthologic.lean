import Lisa.Orthologic.Reference.Search
import Lisa.Combined.Propositional
import Tests.OrderModel
import Tests.OrthologicModel
import Tests.CheckerModel

open Lisa Lisa.Orthologic

open Lisa.Orthologic.Reference

namespace OrthologicTests

def a : Nnf Nat := .lit 0 false
def b : Nnf Nat := .lit 1 false
def c : Nnf Nat := .lit 2 false

-- Exercise lattice laws and the contraction/weakening branch of OL search.
#guard checkLe a a
#guard checkLe (.meet a b) a
#guard checkLe a (.join a b)
#guard checkLe (.meet a (.join a b)) a
#guard checkLe a (.meet a (.join a b))
#guard checkLe (.join (.meet a b) (.meet a c)) (.meet a (.join b c))
#guard checkLe (.meet a a.compl) .bot
#guard checkLe .top (.join a a.compl)
#guard checkLe (.meet (.join a b) (.meet a.compl b.compl)) .bot
#guard checkLe (.join (.meet a b) (.join a.compl b.compl)) .top

-- Reject Boolean-only distributivity and unrelated literals.
#guard !(checkLe a b)
#guard !(checkLe (α := Nat) .top .bot)
#guard !(checkLe (.meet a (.join b c)) (.join (.meet a b) (.meet a c)))
#guard !(checkLe a (.join (.meet a b) (.meet a b.compl)))
#guard !(checkLe (.join a b) (.meet a b))

-- The rejection is required by a genuine ortholattice countermodel.
example : ¬ Orthogonal OrthologicModel.lhs OrthologicModel.rhs.compl := by
  intro h
  apply OrthologicModel.not_distributive
  simpa using h.sound OrthologicModel.valuation

#guard Nnf.smartMeet a a = a
#guard Nnf.smartMeet a .top = a
#guard Nnf.smartMeet a .bot = .bot
#guard Nnf.smartMeet a a.compl = .bot
#guard Nnf.smartJoin a a.compl = .top
#guard Nnf.normalize (.meet a (.join a b)) = a
#guard Nnf.normalize (.join a (.meet a b)) = a
#guard Nnf.normalize (.meet (.join a b) (.meet a.compl b.compl)) = .bot
#guard (Formula.neg (.neg (.atom 0))).normalize = a
#guard (Formula.neg (.meet (.atom 0) (.atom 1))).toNnf = .join a.compl b.compl

-- Check memoized and uncached search, including exhausted depth budgets.
def small : List (Nnf Nat) :=
  [.bot, .top, a, a.compl, b, b.compl, .meet a b, .join a b,
    .meet a a.compl, .join a a.compl, .meet (.join a b) a.compl]

#eval show IO Unit from do
  for fuel in [0, 1, 2, 4, 8] do
    for p in small do
      for q in small do
        unless (searchMemo fuel p q).accepted == search fuel p q do
          throw (IO.userError s!"Memo disagrees at depth {fuel}: {repr p}, {repr q}")

#guard !(searchMemo 0 a a.compl).accepted
#guard (searchMemo 1 a a.compl).accepted

-- Make every atom hash collide; lawful equality still separates the keys.
structure Colliding where
  index : Nat
  deriving DecidableEq

instance : Hashable Colliding := ⟨fun _ => 0⟩

#guard checkLe (.meet (.lit (Colliding.mk 0) false) (.lit (Colliding.mk 1) false))
  (.lit (Colliding.mk 0) false)
#guard !(checkLe (.lit (Colliding.mk 0) false) (.lit (Colliding.mk 1) false))

-- Reify only the exact logical signature, including sort and identifier index.
def p : Expr := .var ⟨⟨"p", 0⟩, prop⟩
def q : Expr := .var ⟨⟨"q", 0⟩, prop⟩
def x : Expr := .var ⟨⟨"x", 0⟩, ind⟩

#guard reify (Expr.imp p q) = .join (.neg (.atom p)) (.atom q)
#guard reify (Expr.iff p q) =
  .meet (.join (.neg (.atom p)) (.atom q)) (.join (.neg (.atom q)) (.atom p))
#guard reify (.const (.named "top" prop 1)) = .atom (.const (.named "top" prop 1))
#guard reify (.const (.named "top" ind)) = .atom (.const (.named "top" ind))
#guard reify (Expr.forall_ ⟨⟨"x", 0⟩, ind⟩ p) =
  .atom (Expr.forall_ ⟨⟨"x", 0⟩, ind⟩ p)
#guard reduceExpr (Expr.and p Expr.top) = p
#guard reduceExpr (Expr.and p (Expr.neg p)) = Expr.bot
#guard reduceExpr x = x
#guard (reduceExpr (Expr.and x Expr.top)).sort = (Expr.and x Expr.top).sort
#guard !(checkExprLe p q)
#guard checkExprLe (Expr.and p q) p

-- Install the reducer through the existing API, without changing kernel rules.
#eval show IO Unit from do
  letI := reduction CheckerModel.leq
  letI := CheckerOrder.of CheckerModel.leq
  let atom : Expr := .const (.named "A" prop)
  let proof : Imported.Checker.LinearProof := #[
    ⟨⟨[atom], [atom]⟩, .hypothesis atom⟩,
    ⟨⟨[Expr.and atom atom], [Expr.and atom Expr.top]⟩, .leftAnd 0 atom atom⟩]
  let invalid : Imported.Checker.LinearProof := #[
    ⟨⟨[atom], [atom]⟩, .hypothesis atom⟩,
    ⟨⟨[Expr.and atom atom], [Expr.const (.named "B" prop)]⟩, .leftAnd 0 atom atom⟩]
  match Imported.Checker.check (leq := CheckerModel.leq) proof,
      Imported.Checker.check (leq := CheckerModel.leq) invalid with
  | .ok _, .error (.atStep 1 .invalidConditions) => pure ()
  | .error e, _ => throw (IO.userError s!"Normalized retained context rejected: {repr e}")
  | _, _ => throw (IO.userError "Normalizer permitted an unrelated context replacement")

-- The reducer is available independently of a particular order model.
example (leq : Order) [OrderAlgebra leq] (φ : Expr) :
    isSame leq (reduceExpr φ) φ := same_reduceExpr φ

example (leq : Order) [OrderAlgebra leq] (φ ψ : Expr)
    (h : checkExprLe φ ψ = true) : leq φ ψ := checkExprLe_sound φ ψ h

example : AlignmentModel.leq (Expr.and p q) p := by
  apply (OrderAlgebra.compare _ _).mpr
  rw [OrderAlgebra.and_eq]
  exact inf_le_left

#print axioms Orthogonal.sound
#print axioms search_proof
#print axioms checkLe_sound
#print axioms Nnf.eval_normalize
#print axioms same_reduceExpr
#print axioms checkExprLe_sound

end OrthologicTests
