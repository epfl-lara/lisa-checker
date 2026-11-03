import Lisa.AlphaBetaEtaNormalization.Syntax
import Lisa.LambdaFol.ToPureFol.SymbolSubstitution
import Lisa.AlphaBetaEtaNormalization.NamedDecision
import Mathlib.ModelTheory.Syntax

namespace Lisa.LambdaFol.Signature
/-- The type of an n-ary first-order symbol with result sort `b`. -/
def arity : Nat → LSort → LSort
  | 0, b => b
  | n + 1, b => ind >> arity n b

end Lisa.LambdaFol.Signature

/-! First-order symbols, bound-variable correspondence, and curried application. -/
namespace Lisa.LambdaFol
open FirstOrder AlphaBetaEtaNormalization
namespace PureFolTranslation
/-- Keep schematic symbols and constants in separate namespaces. -/
structure Symbol where
  schematic : Bool
  id : Identifier
  deriving DecidableEq

def language : Language where
  Functions _ := Symbol
  Relations _ := Symbol

/-- Translate individual de Bruijn indices to PureFol bound-variable levels.
`none` means no corresponding PureFol variable is supplied. -/
abbrev BoundVarMap (n : Nat) := Nat → Option (Fin n)
/-- Under an individual binder, index zero denotes the newest target level. -/
def bind (ρ : BoundVarMap n) : BoundVarMap (n + 1)
  | 0 => some (Fin.last n)
  | k + 1 => (ρ k).map Fin.castSucc

def normalizeExpr? (e : Expr) : Option Packed.Expr :=
  (interpretNamed e Names.free).map (fun ⟨s, t⟩ => ⟨s, normalize t⟩)

/-- Only individual leaves change; the heads of first-order applications stay
the same. Bound variables at other sorts remain bound variables. -/
structure PreservesHeads (R : SymbolSubstitution) : Prop where
  free : ∀ s, s ≠ ind → ∀ x, R.free s x = .free x
  const : ∀ s c, R.const s c = .const c
  bound : ∀ s, s ≠ ind → ∀ i, ∃ j, R.bound s i = .bound j

/-- Reverse the numbering of `n` binders: index `0` becomes level `n - 1`. -/
def indexToLevel (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨n - 1 - i, by omega⟩ else none

@[simp] theorem indexToLevel_zero : indexToLevel 0 = fun _ => none := by funext i; simp [indexToLevel]

theorem indexToLevel_succ (n : Nat) : indexToLevel (n + 1) = bind (indexToLevel n) := by
  funext i
  cases i with
  | zero => simp [indexToLevel, bind, Fin.last]
  | succ i =>
      by_cases hi : i < n
      · simp only [indexToLevel, bind, hi, Nat.succ_lt_succ_iff, ↓reduceDIte, Option.map_some]
        congr 1
        apply Fin.ext
        simp only [Fin.val_castSucc]
        omega
      · simp [indexToLevel, bind, hi]

/-- Abstract a free individual name underneath `n` existing individual binders. -/
def abstractAt (x : Identifier) (n : Nat) : SymbolSubstitution where
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
  apply SymbolSubstitution.ext
  · funext s i
    by_cases hs : s = ind
    · subst s
      cases i with
      | zero => simp [abstractAt, SymbolSubstitution.lift]
      | succ i =>
          by_cases h : n ≤ i <;>
            simp [abstractAt, SymbolSubstitution.lift, Term.shift, Term.rename, Ren.shift, h]
    · simp [abstractAt, SymbolSubstitution.lift, Term.shift, Term.rename, Ren.shift, hs]
  · funext s y
    cases s <;> simp [abstractAt, SymbolSubstitution.lift, Term.shift, Term.rename]
    split <;> rfl
  · funext s c; rfl

theorem abstractAt_zero (x : Identifier) : abstractAt x 0 = SymbolSubstitution.abstract ⟨x, ind⟩ := by
  apply SymbolSubstitution.ext
  · funext s i; simp [abstractAt, SymbolSubstitution.abstract, Sub.ofRen, Ren.shift]
  · funext s y
    cases s <;> simp [abstractAt, SymbolSubstitution.abstract, Names.bind, Names.free, Term.rename]
    by_cases h : y = x
    · subst y; rfl
    · simp [h]
  · rfl

/-- Because the substituted term has no ambient indices, it is unchanged under
the binders encountered while reading a formula. -/
theorem single_lift (x : Identifier) (a : Term ind) (ha : a.shift ind = a) :
    (SymbolSubstitution.single ⟨x, ind⟩ a).lift ind = SymbolSubstitution.single ⟨x, ind⟩ a := by
  apply SymbolSubstitution.ext
  · funext s i; simp [SymbolSubstitution.lift, SymbolSubstitution.single]
  · funext s y
    by_cases h : SVar.mk y s = SVar.mk x ind
    · cases h
      simpa [SymbolSubstitution.lift, SymbolSubstitution.single] using ha
    · simp only [SymbolSubstitution.lift, SymbolSubstitution.single, h, ↓reduceDIte, Term.shift, Term.rename]
  · funext s c; rfl

theorem single_heads (x : Identifier) (a : Term ind) :
    PreservesHeads (SymbolSubstitution.single ⟨x, ind⟩ a) where
  free := by
    intro s hs y
    simp only [SymbolSubstitution.single, show SVar.mk y s ≠ SVar.mk x ind from
      fun h => hs (congrArg SVar.sort h), ↓reduceDIte]
  const _ _ := rfl
  bound := by intros; exact ⟨_, rfl⟩

end PureFolTranslation
namespace Embedding
open Signature
def apps : (n : Nat) → Term (arity n s) → (Fin n → Term ind) → Term s
  | 0, f, _ => f
  | n + 1, f, ts => apps n (.app f (ts 0)) (fun i => ts i.succ)

theorem apps_replace (R : SymbolSubstitution) (n : Nat) (f : Term (arity n s)) (ts : Fin n → Term ind) :
    R.apply (apps n f ts) = apps n (R.apply f) (fun i => R.apply (ts i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [apps, ih, SymbolSubstitution.apply]; rfl

def head (c : PureFolTranslation.Symbol) (s : LSort) : Term s :=
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
end Lisa.LambdaFol
