import Lisa.Orthologic.ExpressionModel
import Lisa.Order
import Mathlib.Order.BooleanAlgebra.Defs

open Lisa Expr

namespace AlignmentModel

instance : Ortholattice Bool where
  toLattice := inferInstance
  toBoundedOrder := inferInstance
  toCompl := inferInstance
  compl_antitone := by decide
  compl_involutive := by intro a; cases a <;> rfl
  sup_compl := by decide

-- Interpret logical constructors; leave other syntax uninterpreted.
def value : Expr → Bool
  | .var x => x.id.idx % 2 == 0
  | .const c => c == SConst.named "top" prop
  | .app (.const c) p =>
      if c == SConst.named "not" (prop >> prop) then !(value p) else false
  | .app (.app (.const c) p) q =>
      if c == SConst.named "and" (prop >> prop >> prop) then value p && value q
      else if c == SConst.named "or" (prop >> prop >> prop) then value p || value q
      else if c == SConst.named "imp" (prop >> prop >> prop) then !(value p) || value q
      else if c == SConst.named "iff" (prop >> prop >> prop) then
        (!(value p) || value q) && (!(value q) || value p)
      else false
  | _ => false

def leq (p q : Expr) : Prop := value p ≤ value q

def interpretation : Lisa.Orthologic.Interpretation leq where
  Carrier := Bool
  algebra := inferInstance
  eval := value
  compare := fun _ _ => Iff.rfl
  top_eq := by decide
  bot_eq := by decide
  and_eq := by intros; rfl
  or_eq := by intros; rfl
  neg_eq := by intros; rfl
  imp_eq := by intros; rfl
  iff_eq := by intros; rfl

instance : IsPreorder Expr leq := interpretation.preorder
instance : SequentEncoding leq := interpretation.sequentEncoding

-- Identity reduction witnesses the strict matching option without collapsing atoms.
instance : OrderReduction leq where
  reduce := id
  preserves := fun _ => ⟨le_rfl, le_rfl⟩
  preservesSort := fun _ => rfl
  reflect p q h := by cases h; exact ⟨le_rfl, le_rfl⟩

instance : RelationCongruence leq where
  imp_congr := interpretation.imp_congr
  eq_congr := by
    intro s s' t t' _ _ _ _ _ _
    exact ⟨le_rfl, le_rfl⟩

example : ¬ leq top bot := by unfold leq; decide
example : isSame leq (and top top) top := by unfold isSame leq; decide
example : ¬ reducedSame leq (and top top) top := by
  change and top top ≠ top
  decide

-- An equivalence-preserving reduction need not be syntactically idempotent.
def doubleNeg (p : Expr) : Expr :=
  if p.sort = some prop then neg (neg p) else p

@[reducible] def doubleNegReduction (order : ExprRel) (m : Lisa.Orthologic.Interpretation order) : OrderReduction order :=
  letI := m.preorder
  OrderReduction.of doubleNeg (by
    intro p
    unfold doubleNeg
    split
    · exact m.double_neg p
    · exact m.same_refl p) (by
    intro p
    unfold doubleNeg
    split
    · rename_i h
      simp [Expr.neg, h]
    · rfl)

example : doubleNeg top ≠ top := by decide
example : doubleNeg (doubleNeg top) ≠ doubleNeg top := by decide
example : doubleNeg (.var ⟨⟨"x", 0⟩, ind⟩) = .var ⟨⟨"x", 0⟩, ind⟩ := by decide

example (p q : Expr) :
    isSame leq (doubleNeg (and p q)) (and (doubleNeg p) (doubleNeg q)) := by
  letI := doubleNegReduction leq interpretation
  exact interpretation.map_reduce_and p q

example (p q : Expr) (h : leq p q) : leq (doubleNeg p) (doubleNeg q) := by
  letI := doubleNegReduction leq interpretation
  exact OrderReduction.monotone h

example (p q : Expr) (h : doubleNeg p = doubleNeg q) : isSame leq p q := by
  letI := doubleNegReduction leq interpretation
  exact OrderReduction.sound p q h

example : ¬ isSame leq top bot := by unfold isSame leq; decide

instance : ProofOrder leq := ProofOrder.of _

end AlignmentModel
