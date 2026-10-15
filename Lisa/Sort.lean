import Mathlib.Init

/-! Shared sorts and symbols for named expressions and intrinsically typed terms. -/

namespace Lisa

structure Identifier where
  name : String
  idx : Nat := 0
deriving DecidableEq, Repr, Inhabited, Hashable

inductive LSort where
  | ind : LSort
  | prop : LSort
  | arrow : LSort -> LSort -> LSort
with
  /-- Store the structural hash when constructing a sort. -/
  @[computed_field] cachedHash : LSort → UInt64
    | .ind => 0
    | .prop => 1
    | .arrow a b => mixHash (mixHash 2 a.cachedHash) b.cachedHash
deriving DecidableEq, Repr, Inhabited

instance : Hashable LSort := ⟨LSort.cachedHash⟩

abbrev prop : LSort := .prop
abbrev ind : LSort := .ind

infixr:60 " >> " => LSort.arrow

namespace LSort

def isFunctional : LSort -> Bool
  | ind => true
  | prop => false
  | arrow ind s => isFunctional s
  | arrow _ _ => false

def isPredicate : LSort -> Bool
  | ind => false
  | prop => true
  | arrow ind s => isPredicate s
  | arrow _ _ => false

def depth : LSort -> Nat
  | ind => 0
  | prop => 0
  | arrow _ s => depth s + 1

def splitArgs : LSort -> (List LSort × LSort)
  | ind => ([], ind)
  | prop => ([], prop)
  | arrow arg res =>
      match splitArgs res with
      | (args, final) => (arg :: args, final)

end LSort

structure SVar where
  id : Identifier
  sort : LSort
deriving DecidableEq, Repr, Inhabited, Hashable

structure SConst where
  id : Identifier
  sort : LSort
deriving DecidableEq, Repr, Inhabited, Hashable

end Lisa
