import Lisa.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union

namespace Lisa

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

@[simp]
def wellSorted (e : Expr) : Prop := e.sort.isSome

@[simp]
def hasSort (e : Expr) (s : LSort) : Prop := e.sort = some s

def isFunctional (e : Expr) : Prop := e.sort.map LSort.isFunctional = some true

def isPredicate (e : Expr) : Prop := e.sort.map LSort.isPredicate = some true

end Expr

@[simp]
def isFormula (e : Expr) : Prop := e.hasSort prop

@[simp]
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

@[simp]
def wellSorted : Subst -> Prop
  | .nil => True
  | .cons x e rest => e.hasSort x.sort ∧ wellSorted rest

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

@[simp]
theorem wellSorted_replace {σ : Subst} {x : SVar} {e : Expr}
    (hσ : wellSorted σ) (he : e.hasSort x.sort) :
    wellSorted (σ.replace x e) := by
  induction σ with
  | nil =>
      simp [Lean.AssocList.replace]
  | cons y v rest ih =>
      simp [Lean.AssocList.replace] at hσ ⊢
      by_cases hyx : (y == x) = true
      · simp [hyx, hσ]
        have hyxEq : y = x := beq_iff_eq.mp hyx
        subst hyxEq
        exact he
      · have hyxFalse : (y == x) = false := by
          cases h : y == x <;> simp [h] at hyx ⊢
        simp [hyxFalse, hσ, ih hσ.2]

@[simp]
theorem wellSorted_insert {σ : Subst} {x : SVar} {e : Expr}
    (hσ : wellSorted σ) (he : e.hasSort x.sort) :
    wellSorted (σ.insert x e) := by
  unfold Lean.AssocList.insert
  by_cases hcontains : Lean.AssocList.contains x σ = true
  · simp [hcontains, wellSorted_replace hσ he]
  · simp [hcontains, Lean.AssocList.insertNew, hσ]
    exact he

theorem subst_preserves_sort {σ : Subst} (hσ : wellSorted σ) :
    ∀ e, (subst σ e).sort = e.sort := by
  intro e
  induction e generalizing σ with
  | var x =>
      simp [subst]
      cases hfind : σ.find? x with
      | none =>
          simp
      | some v =>
          induction σ with
          | nil =>
              simp [Lean.AssocList.find?] at hfind
          | cons y w rest ih =>
              simp [Lean.AssocList.find?] at hfind hσ
              by_cases hyx : (y == x) = true
              · simp [hyx] at hfind
                cases hfind
                have hyxEq : y = x := beq_iff_eq.mp hyx
                subst hyxEq
                exact hσ.1
              · have hyxFalse : (y == x) = false := by
                  cases h : y == x <;> simp [h] at hyx ⊢
                simp [hyxFalse] at hfind
                exact ih hσ.2 hfind
  | const c =>
      simp [subst]
  | app f a ihf iha =>
      simp [subst, ihf hσ, iha hσ]
  | lam x body ih =>
      dsimp [subst, Expr.sort]
      set x' :=
        if x ∈ σ.freeVars then
          { id := freshId (Finset.image (fun x => x.id) σ.freeVars) x.id, sort := x.sort }
        else
          x
      have hxsort : x'.sort = x.sort := by
        dsimp [x']
        split <;> rfl
      have hvar : (Expr.var x').hasSort x.sort := by
        simp [Expr.hasSort, hxsort]
      rw [ih (wellSorted_insert hσ hvar)]
      cases body.sort <;> simp [hxsort]

theorem subst_preserves_hasSort {σ : Subst} (hσ : wellSorted σ)
    {e : Expr} {s : LSort} (h : e.hasSort s) :
    (subst σ e).hasSort s := by
  rw [Expr.hasSort, subst_preserves_sort hσ e]
  exact h

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
