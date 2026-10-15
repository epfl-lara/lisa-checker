import Lisa.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Fold

namespace Lisa

inductive Expr where
  | var : SVar -> Expr
  | const : SConst -> Expr
  | app : Expr -> Expr -> Expr
  | lam : SVar -> Expr -> Expr
with
  /-- Store the structural hash when constructing an expression. -/
  @[computed_field] cachedHash : Expr → UInt64
    | .var x => mixHash 0 (hash x)
    | .const c => mixHash 1 (hash c)
    | .app f a => mixHash (mixHash 2 f.cachedHash) a.cachedHash
    | .lam x body => mixHash (mixHash 3 (hash x)) body.cachedHash
deriving DecidableEq, Repr, Inhabited

instance : Hashable Expr := ⟨Expr.cachedHash⟩

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

/-- Increment the largest used index with the base name, including the base index. -/
def freshId (used : Finset Identifier) (base : Identifier) : Identifier :=
  let maxIdx := (used.filter (·.name = base.name)).fold Nat.max base.idx (·.idx)
  { base with idx := maxIdx + 1 }

theorem freshId_not_mem (used : Finset Identifier) (base : Identifier) :
    freshId used base ∉ used := by
  intro h
  have hmem : freshId used base ∈ used.filter (·.name = base.name) :=
    Finset.mem_filter.mpr ⟨h, rfl⟩
  have hbound : (freshId used base).idx ≤
      (used.filter (·.name = base.name)).fold Nat.max base.idx (·.idx) := by
    rw [Finset.le_fold_max]
    exact Or.inr ⟨_, hmem, le_rfl⟩
  exact Nat.not_succ_le_self _ hbound

abbrev Subst : Type := Lean.AssocList SVar Expr

namespace Subst

def freeVars (σ : Subst) : Finset SVar :=
  σ.toList.foldl (fun acc (x, e) => acc ∪ {x} ∪ e.freeVars) ∅

/-- Collect free variables of replacement expressions. -/
def rangeFreeVars : Subst → Finset SVar
  | .nil => ∅
  | .cons _ e rest => e.freeVars ∪ rangeFreeVars rest

/-- Collect the variables replaced by a substitution. -/
def domain : Subst → Finset SVar
  | .nil => ∅
  | .cons x _ rest => insert x (domain rest)

/-- Remove a variable from the substitution, including shadowed entries. -/
def without (x : SVar) : Subst → Subst
  | .nil => .nil
  | .cons y e rest =>
      if y = x then without x rest else .cons y e (without x rest)

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
      let fv := σ.rangeFreeVars
      let remaining := σ.without x
      if x ∈ fv then
        let taken := fv ∪ body.freeVars ∪ σ.domain
        let x' := { x with id := freshId (taken.image (·.id)) x.id }
        .lam x' (subst (remaining.insert x (.var x')) body)
      else
        .lam x (subst remaining body)

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

@[simp]
theorem wellSorted_without {σ : Subst} (hσ : wellSorted σ) (x : SVar) :
    wellSorted (σ.without x) := by
  induction σ with
  | nil => trivial
  | cons y e rest ih =>
      simp only [wellSorted] at hσ
      simp only [without]
      cases hσ
      split <;> simp [*]
      assumption

theorem subst_preserves_sort {σ : Subst} (hσ : wellSorted σ) :
    ∀ e, (subst σ e).sort = e.sort := by
  intro e
  induction e generalizing σ with
  | var x =>
      simp [subst]
      cases hfind : σ.find? x with
      | none =>
          -- x ∉ σ
          simp
      | some v =>
          induction σ with
          | nil =>
              -- contradiction, empty subst
              simp [Lean.AssocList.find?] at hfind
          | cons y w rest ih =>
              -- x ∈ σ
              simp [Lean.AssocList.find?] at hfind hσ
              by_cases hyx : y == x
              · -- x at head
                simp [hyx] at hfind
                have hyxEq : y = x := beq_iff_eq.mp hyx
                subst hfind hyxEq
                exact hσ.1
              · -- x in tail
                simp [hyx] at hfind
                simp [*]
  | const c =>
      simp [subst]
  | app f a ihf iha =>
      simp [subst, ihf hσ, iha hσ]
  | lam x body ih =>
      simp only [subst]
      split
      · simp only [Expr.sort]
        rw [ih (wellSorted_insert (wellSorted_without hσ x) (by rfl))]
      · simp only [Expr.sort]
        rw [ih (wellSorted_without hσ x)]

theorem subst_preserves_hasSort {σ : Subst} (hσ : wellSorted σ)
    {e : Expr} {s : LSort} (h : e.hasSort s) :
    (subst σ e).hasSort s := by
  simp [Expr.hasSort, subst_preserves_sort, *]
  assumption

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
