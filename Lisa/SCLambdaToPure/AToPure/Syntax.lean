import Lisa.Lambda.Syntax
import Lisa.SCLambdaToPure.AToPure.Replacement
import Lisa.Lambda.NamedDecision
import Mathlib.ModelTheory.Syntax

namespace Lisa.SCLambdaToPure.Signature
/-- The type of an n-ary first-order symbol with result sort `b`. -/
def arity : Nat → LSort → LSort
  | 0, b => b
  | n + 1, b => ind >> arity n b

end Lisa.SCLambdaToPure.Signature

/-! Shared signature, binding and application helpers.
This file has no dependency on a proof calculus or a target reader. -/
namespace Lisa.SCLambdaToPure
open FirstOrder Lambda
namespace Readback
/-- Keep schematic symbols and constants in separate namespaces. -/
structure Symbol where
  schematic : Bool
  id : Identifier
  deriving DecidableEq

def language : Language where
  Functions _ := Symbol
  Relations _ := Symbol

abbrev Bound (n : Nat) := Nat → Option (Fin n)
/-- Under an individual binder, index zero denotes the newest target level. -/
def bind (ρ : Bound n) : Bound (n + 1)
  | 0 => some (Fin.last n)
  | k + 1 => (ρ k).map Fin.castSucc

def normalized (e : Expr) : Option Packed.Expr :=
  (interpretNamed e Names.free).map (fun ⟨s, t⟩ => ⟨s, normalize t⟩)

theorem normalized_eq {e f : Expr} (h : AlphaBetaEta e f) :
    normalized e = normalized f := by
  have he := interpretNamed_alphaBetaEta h Names.free
  unfold normalized
  generalize interpretNamed e Names.free = a at he ⊢
  generalize interpretNamed f Names.free = b at he ⊢
  cases he with
  | none => rfl
  | some he =>
      simp only [Option.map_some, normalize_eq_of_equiv he]

/-- Only individual leaves change; the heads of first-order applications stay
the same. Bound variables at other sorts remain bound variables. -/
structure PreservesHeads (R : Replacement) : Prop where
  free : ∀ s, s ≠ ind → ∀ x, R.free s x = .free x
  const : ∀ s c, R.const s c = .const c
  bound : ∀ s, s ≠ ind → ∀ i, ∃ j, R.bound s i = .bound j

/-- The in-scope Lisa indices, translated to target levels. -/
def scope (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨n - 1 - i, by omega⟩ else none

@[simp] theorem scope_zero : scope 0 = fun _ => none := by funext i; simp [scope]

theorem scope_succ (n : Nat) : scope (n + 1) = bind (scope n) := by
  funext i
  cases i with
  | zero => simp [scope, bind, Fin.last]
  | succ i =>
      by_cases hi : i < n
      · simp only [scope, bind, hi, Nat.succ_lt_succ_iff, ↓reduceDIte, Option.map_some]
        congr 1
        apply Fin.ext
        simp only [Fin.val_castSucc]
        omega
      · simp [scope, bind, hi]

/-- Abstract a free individual name underneath `n` existing individual binders. -/
def abstractAt (x : Identifier) (n : Nat) : Replacement where
  bound s i := .bound (if s = ind ∧ n ≤ i then i + 1 else i)
  free
    | .ind, y => if y = x then .bound n else .free y
    | .prop, y => .free y
    | .arrow _ _, y => .free y
  const _ c := .const c

theorem abstractAt_heads (x : Identifier) (n : Nat) : PreservesHeads (abstractAt x n) where
  free := by intro s hs y; cases s <;> simp_all [abstractAt]
  const _ _ := rfl
  bound := by intros; exact ⟨_, rfl⟩

theorem abstractAt_lift (x : Identifier) (n : Nat) :
    abstractAt x (n + 1) = (abstractAt x n).lift ind := by
  apply Replacement.ext
  · funext s i
    by_cases hs : s = ind
    · subst s
      cases i with
      | zero => simp [abstractAt, Replacement.lift]
      | succ i =>
          by_cases h : n ≤ i <;>
            simp [abstractAt, Replacement.lift, Term.shift, Term.rename, Ren.shift, h]
    · simp [abstractAt, Replacement.lift, Term.shift, Term.rename, Ren.shift, hs]
  · funext s y
    cases s <;> simp [abstractAt, Replacement.lift, Term.shift, Term.rename]
    split <;> rfl
  · funext s c; rfl

theorem abstractAt_zero (x : Identifier) : abstractAt x 0 = Replacement.abstract ⟨x, ind⟩ := by
  apply Replacement.ext
  · funext s i; simp [abstractAt, Replacement.abstract, Sub.ofRen, Ren.shift]
  · funext s y
    cases s <;> simp [abstractAt, Replacement.abstract, Names.bind, Names.free, Term.rename]
    by_cases h : y = x
    · subst y; rfl
    · simp [h]
  · rfl

/-- Because the substituted term has no ambient indices, it is unchanged under
the binders encountered while reading a formula. -/
theorem single_lift (x : Identifier) (a : Term ind) (ha : a.shift ind = a) :
    (Replacement.single ⟨x, ind⟩ a).lift ind = Replacement.single ⟨x, ind⟩ a := by
  apply Replacement.ext
  · funext s i; simp [Replacement.lift, Replacement.single]
  · funext s y
    by_cases h : SVar.mk y s = SVar.mk x ind
    · cases h
      simpa [Replacement.lift, Replacement.single] using ha
    · simp only [Replacement.lift, Replacement.single, h, ↓reduceDIte, Term.shift, Term.rename]
  · funext s c; rfl

theorem single_heads (x : Identifier) (a : Term ind) :
    PreservesHeads (Replacement.single ⟨x, ind⟩ a) where
  free := by
    intro s hs y
    simp only [Replacement.single, show SVar.mk y s ≠ SVar.mk x ind from
      fun h => hs (congrArg SVar.sort h), ↓reduceDIte]
  const _ _ := rfl
  bound := by intros; exact ⟨_, rfl⟩

end Readback
namespace Embedding
open Signature
def apps : (n : Nat) → Term (arity n s) → (Fin n → Term ind) → Term s
  | 0, f, _ => f
  | n + 1, f, ts => apps n (.app f (ts 0)) (fun i => ts i.succ)

theorem apps_replace (R : Replacement) (n : Nat) (f : Term (arity n s)) (ts : Fin n → Term ind) :
    R.apply (apps n f ts) = apps n (R.apply f) (fun i => R.apply (ts i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [apps, ih, Replacement.apply]; rfl

def head (c : Readback.Symbol) (s : LSort) : Term s :=
  if c.schematic then .free c.id else .const c.id

theorem mem_apps {x : SVar} (n : Nat) (f : Term (arity n s)) (ts : Fin n → Term ind)
    (h : x ∈ (apps n f ts).freeVars) : x ∈ f.freeVars ∨ ∃ i, x ∈ (ts i).freeVars := by
  induction n with
  | zero => exact .inl h
  | succ n ih =>
      rcases ih _ _ h with h | ⟨i, hi⟩
      · rcases Finset.mem_union.mp h with hf | ht
        · exact .inl hf
        · exact .inr ⟨0, ht⟩
      · exact .inr ⟨i.succ, hi⟩

end Embedding
end Lisa.SCLambdaToPure
