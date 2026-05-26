import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union

namespace Lisa

structure Identifier where
  name : String
  idx : Nat := 0
deriving DecidableEq, Repr, Inhabited

inductive LSort where
  | ind : LSort
  | prop : LSort
  | arrow : LSort -> LSort -> LSort
deriving DecidableEq, Repr, Inhabited

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
deriving DecidableEq, Repr, Inhabited

structure SConst where
  id : Identifier
  sort : LSort
deriving DecidableEq, Repr, Inhabited

inductive Expr where
  | var : SVar -> Expr
  | const : SConst -> Expr
  | app : Expr -> Expr -> Expr
  | lam : SVar -> Expr -> Expr
deriving DecidableEq, Repr, Inhabited

namespace Expr

@[simp]
def freeVars : Expr -> Finset SVar
  | .var x => {x}
  | .const _ => ∅
  | .app f a => f.freeVars ∪ a.freeVars
  | .lam x body => body.freeVars \ {x}

@[simp]
def sort : Expr -> Option LSort
  | .var x => some x.sort
  | .const c => some c.sort
  | .app f a =>
      match sort f with
      | some (.arrow argSort resSort) =>
          match sort a with
          | some aSort => if aSort = argSort then some resSort else none
          | none => none
      | _ => none
  | .lam x body =>
      match sort body with
      | some bodySort => some (x.sort >> bodySort)
      | none => none

def wellSorted (e : Expr) : Prop := e.sort.isSome

def hasSort (e : Expr) (s : LSort) : Prop := e.sort = some s

def isFunctional (e : Expr) : Prop := e.sort.map LSort.isFunctional = some true

def isPredicate (e : Expr) : Prop := e.sort.map LSort.isPredicate = some true

end Expr

def isFormula (e : Expr) : Prop := e.hasSort prop

def isTerm (e : Expr) : Prop := e.hasSort ind

@[simp]
def isFSet (Γ : Finset Expr) : Prop := ∀ φ ∈ Γ, isFormula φ

/-- Given a set of used identifiers and a base identifier, generate a fresh
identifier with same name as base. -/
def freshId (used : Finset Identifier) (base : Identifier) : Identifier :=
  let maxIdx := used.fold Nat.max 0 (·.idx)
  { base with idx := maxIdx + 1 }

abbrev Subst : Type := Lean.AssocList SVar Expr

namespace Subst

def freeVars (σ : Subst) : Finset SVar :=
  σ.toList.foldl (fun acc (x, e) => acc ∪ {x} ∪ e.freeVars) ∅

def wellSorted (σ : Subst) : Prop :=
  ∀ x e, σ.find? x = some e -> e.hasSort x.sort

/-- Capture-avoiding simultaneous substitution. -/
def subst (σ : Subst) : Expr -> Expr
  | .var x =>
      match σ.find? x with
      | some e => e
      | none => .var x
  | .const c => .const c
  | .app f a => .app (subst σ f) (subst σ a)
  | .lam x body =>
      let fv := σ.freeVars
      let x' :=
        if x ∈ fv then
          let id := freshId (fv.image (·.id)) x.id
          { x with id }
        else
          x
      .lam x' (subst (σ.insert x (.var x')) body)

end Subst

namespace SConst

@[simp]
def named (name : String) (sort : LSort) (idx : Nat := 0) : SConst :=
  { id := { name, idx }, sort }

end SConst

namespace Expr

def applied (e : Expr) (args : List Expr) : Expr :=
  args.foldl .app e

def top : Expr := .const (.named "top" prop)

def bot : Expr := .const (.named "bot" prop)

def neg (p : Expr) : Expr :=
  .app (.const (.named "not" (prop >> prop))) p

def imp (p q : Expr) : Expr :=
  .app (.app (.const (.named "imp" (prop >> prop >> prop))) p) q

def iff (p q : Expr) : Expr :=
  .app (.app (.const (.named "iff" (prop >> prop >> prop))) p) q

def and (p q : Expr) : Expr :=
  .app (.app (.const (.named "and" (prop >> prop >> prop))) p) q

def or (p q : Expr) : Expr :=
  .app (.app (.const (.named "or" (prop >> prop >> prop))) p) q

def eq (s t : Expr) : Expr :=
  .app (.app (.const (.named "eq" (ind >> ind >> prop))) s) t

def forall_ (x : SVar) (p : Expr) : Expr :=
  .app (.const (.named "forall" ((ind >> prop) >> prop))) (.lam x p)

def exists_ (x : SVar) (p : Expr) : Expr :=
  .app (.const (.named "exists" ((ind >> prop) >> prop))) (.lam x p)

def epsilon_ (p : Expr) : Expr :=
  .app (.const (.named "epsilon" ((ind >> prop) >> ind))) p

def subst (σ : Subst) (φ : Expr) : Expr :=
  σ.subst φ

def substOne (x : SVar) (t : Expr) (φ : Expr) : Expr :=
  subst ((∅: Subst).insert x t) φ

end Expr

class HasFree (α : Type) where
  freeVars : α -> Finset SVar

abbrev freeVars := @HasFree.freeVars

instance : HasFree Expr where
  freeVars := Expr.freeVars

instance : HasFree (Finset Expr) where
  freeVars Γ := Γ.biUnion freeVars

end Lisa
