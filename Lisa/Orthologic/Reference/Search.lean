import Lisa.Orthologic.Orthogonal
import Std.Data.DHashMap.Basic

/-!
Use two-formula, cut-free orthologic search. Contraction detects a formula
below its own complement; weakening then permits any second formula.

The search follows Simon Guilloud's `orthologic-coq` development, but works
directly on negation normal forms and treats bounds as primitive constructors.
-/

namespace Lisa.Orthologic.Reference

open Nnf

/-- Retain a Boolean answer and erase its soundness certificate at compilation. -/
structure Answer {α : Type} (p q : Nnf α) where
  accepted : Bool
  proof : accepted = true → Orthogonal p q

namespace Answer

def reject {α : Type} (p q : Nnf α) : Answer p q := ⟨false, by simp⟩

def accept {α : Type} {p q : Nnf α} (h : Orthogonal p q) : Answer p q :=
  ⟨true, fun _ => h⟩

def map {α : Type} {p q r s : Nnf α} (f : Orthogonal p q → Orthogonal r s)
    (answer : Answer p q) : Answer r s := ⟨answer.accepted, fun h => f (answer.proof h)⟩

end Answer

private def project {α : Type} {m : Type → Type} [Monad m]
    (rec : (p q : Nnf α) → m (Answer p q)) (p q : Nnf α) : m (Answer p q) := do
  match p with
  | .meet a b =>
      let first ← rec a q
      if first.accepted then return first.map Orthogonal.meetLeft
      return (← rec b q).map Orthogonal.meetRight
  | p => return .reject p q

private def contract {α : Type} {m : Type → Type} [Monad m]
    (rec : (p q : Nnf α) → m (Answer p q)) (p q : Nnf α) : m (Answer p q) := do
  match p with
  | .meet a b => return (← rec (.meet a b) (.meet a b)).map Orthogonal.weaken
  | p => return .reject p q

/-- Share the same short-circuiting rules between plain and memoized search. -/
private def searchStep {α : Type} [DecidableEq α] {m : Type → Type} [Monad m]
    (rec : (p q : Nnf α) → m (Answer p q)) (p q : Nnf α) : m (Answer p q) := do
  if h : p = q.compl then
    return .accept (by subst p; simpa using Orthogonal.ax q.compl)
  match p, q with
  | .bot, _ => return .accept (.bot _)
  | _, .bot => return .accept (.symm (.bot _))
  | .join a b, q =>
      let first ← rec a q
      if h : first.accepted = true then
        return (← rec b q).map (Orthogonal.join (first.proof h))
      return .reject _ _
  | p, .join a b =>
      let first ← rec p a
      if h : first.accepted = true then
        return (← rec p b).map (fun last =>
          .symm (.join (.symm (first.proof h)) (.symm last)))
      return .reject _ _
  | p, q =>
      let first ← project rec p q
      if first.accepted then return first
      let second ← project rec q p
      if second.accepted then return second.map Orthogonal.symm
      let third ← contract rec p q
      if third.accepted then return third
      return (← contract rec q p).map Orthogonal.symm

/-- Search with an explicit depth budget. Failure is not a refutation. -/
def probe {α : Type} [DecidableEq α] : (fuel : Nat) → (p q : Nnf α) → Answer p q
  | 0, p, q => .reject p q
  | fuel + 1, p, q => Id.run (searchStep (fun a b => pure (probe fuel a b)) p q)

def search {α : Type} [DecidableEq α] (fuel : Nat) (p q : Nnf α) : Bool :=
  (probe fuel p q).accepted

theorem search_proof {α : Type} [DecidableEq α] (fuel : Nat) (p q : Nnf α)
    (h : search fuel p q = true) : Orthogonal p q := (probe fuel p q).proof h

/-- Key cached answers by depth as well as formulas; keep proof fields erased. -/
abbrev Memo (α : Type) [DecidableEq α] [Hashable α] :=
  Std.DHashMap (Nat × Nnf α × Nnf α) (fun key => Answer key.2.1 key.2.2)

/-- Memoize subproblems in a standard dependent hash map. -/
def probeMemo {α : Type} [DecidableEq α] [Hashable α] :
    Nat → (p q : Nnf α) → StateM (Memo α) (Answer p q)
  | 0, p, q => pure (.reject p q)
  | fuel + 1, p, q => do
      let key := (fuel + 1, p, q)
      if let some answer := (← get).get? key then return answer
      let answer ← searchStep (probeMemo fuel) p q
      modify (·.insert key answer)
      return answer

/-- Scope the memo table to one query, retaining neither atoms nor trees globally. -/
def searchMemo {α : Type} [DecidableEq α] [Hashable α]
    (fuel : Nat) (p q : Nnf α) : Answer p q :=
  (probeMemo fuel p q).run' ∅

theorem search_sound {α L : Type} [DecidableEq α] [Ortholattice L]
    (v : α → L) (fuel : Nat) (p q : Nnf α) (h : search fuel p q = true) :
    p.eval v ≤ (q.eval v)ᶜ := (search_proof fuel p q h).sound v

/-- Check an inequality by searching against the complement of its right side. -/
def checkLe {α : Type} [DecidableEq α] [Hashable α] (p q : Nnf α) : Bool :=
  (searchMemo (2 * (p.size + q.size) + 1) p q.compl).accepted

theorem checkLe_sound {α L : Type} [DecidableEq α] [Hashable α] [Ortholattice L]
    (v : α → L) (p q : Nnf α) (h : checkLe p q = true) : p.eval v ≤ q.eval v := by
  simpa using (searchMemo _ p q.compl).proof h |>.sound v

end Lisa.Orthologic.Reference
