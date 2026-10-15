import Lisa.Checker
import Mathlib.Order.BooleanAlgebra.Defs

open Lisa Expr

namespace CheckerModel

instance : Ortholattice (Fin 8 → Bool) where
  toLattice := inferInstance
  toBoundedOrder := inferInstance
  toCompl := inferInstance
  compl_antitone := by intro p q h v; exact compl_le_compl (h v)
  compl_involutive := by intro p; funext v; exact compl_compl (p v)
  sup_compl := by intro p; funext v; exact sup_compl_eq_top

def value (v : Fin 8) : Expr → Bool
  | .var x => v.val.testBit (x.id.idx % 3)
  | .const c =>
    if c == SConst.named "top" prop then true
    else if c == SConst.named "A" prop then v.val.testBit 0
    else if c == SConst.named "B" prop then v.val.testBit 1
    else if c == SConst.named "C" prop then v.val.testBit 2
    else false
  | .app (.const c) p =>
    if c == SConst.named "not" (prop >> prop) then !(value v p)
    else if c == SConst.named "F" (ind >> prop) then
      v.val.testBit (if p == Expr.const (.named "t" ind) then 1 else 2)
    else false
  | .app (.app (.const c) p) q =>
    if c == SConst.named "and" (prop >> prop >> prop) then value v p && value v q
    else if c == SConst.named "or" (prop >> prop >> prop) then value v p || value v q
    else if c == SConst.named "imp" (prop >> prop >> prop) then !(value v p) || value v q
    else if c == SConst.named "iff" (prop >> prop >> prop) then
      (!(value v p) || value v q) && (!(value v q) || value v p)
    else v.val.testBit 0
  | _ => false

def leq (p q : Expr) : Prop := ∀ v : Fin 8, value v p ≤ value v q

instance : DecidableRel leq := fun p q =>
  inferInstanceAs (Decidable (∀ v : Fin 8, value v p ≤ value v q))

instance : OrderAlgebra leq where
  Carrier := Fin 8 → Bool
  algebra := inferInstance
  eval p := fun v => value v p
  compare := fun _ _ => Iff.rfl
  top_eq := rfl
  bot_eq := rfl
  and_eq := by intros; rfl
  or_eq := by intros; rfl
  neg_eq := by intros; rfl
  imp_eq := by intros; rfl
  iff_eq := by intros; rfl

instance : OrderReduction leq where
  reduce := id
  preserves := fun _ => ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  preservesSort := fun _ => rfl

instance : CheckerOrder leq := CheckerOrder.of _
instance : ImportOrder leq := ImportOrder.of _

end CheckerModel
