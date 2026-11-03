import Lisa.SCLambdaToPure.Bridge
import Lisa.SCLambdaToPure.A
import Mathlib.Logic.Encodable.Basic

/-!
# Reading first-order canonical expressions into Mathlib syntax

Only the first-order fragment is read here. A remaining higher-order application
or epsilon term returns `none`; it is never turned into an opaque atom. Free
schematic function/predicate symbols with individual arguments are preserved as
first-order symbols, separately from constants. Bound indices are translated
from Lisa's per-sort indices to Mathlib's levels.
-/

namespace Lisa.SCLambdaToPure.Readback

open FirstOrder Lambda

abbrev BTerm (n : Nat) := language.Term (Nat ⊕ Fin n)
abbrev BFormula (n : Nat) := language.BoundedFormula Nat n

mutual
  /-- Read an individual term. All arguments of a first-order symbol are individuals. -/
  def term (ρ : Bound n) : Term ind → Option (BTerm n)
    | .bound k => (ρ k).map (fun i => .var (.inr i))
    | .free x => some (.var (.inl (variableCode x)))
    | .const c => some (.func ⟨false, c⟩ Fin.elim0)
    | .app (s := .ind) f a => do
        let (symbol, args) ← spine ρ f
        let a' ← term ρ a
        let args := args ++ [a']
        return .func symbol args.get
    | .app (s := .prop) _ _ => none
    | .app (s := .arrow _ _) _ _ => none

  /-- Collect the head and individual arguments of a partially applied symbol. -/
  def spine (ρ : Bound n) : Term s → Option (Symbol × List (BTerm n))
    | .free x => some (⟨true, x⟩, [])
    | .const c => some (⟨false, c⟩, [])
    | .app (s := .ind) f a => do
        let (symbol, args) ← spine ρ f
        let a' ← term ρ a
        return (symbol, args ++ [a'])
    | _ => none
end

/-- Read a formula after eta-long normalization. Recognition includes sorts and
the complete identifier, just as it does in the production normalizer. -/
def formula (ρ : Bound n) : Term prop → Option (BFormula n)
  | .const ⟨"top", 0⟩ => some ⊤
  | .const ⟨"bot", 0⟩ => some ⊥
  | .app (s := .prop) (.const ⟨"not", 0⟩) p => return (← formula ρ p).not
  | .app (s := .prop) (.app (s := .prop) (.const ⟨"and", 0⟩) p) q =>
      return (← formula ρ p) ⊓ (← formula ρ q)
  | .app (s := .prop) (.app (s := .prop) (.const ⟨"or", 0⟩) p) q =>
      return (← formula ρ p) ⊔ (← formula ρ q)
  | .app (s := .prop) (.app (s := .prop) (.const ⟨"imp", 0⟩) p) q =>
      return (← formula ρ p).imp (← formula ρ q)
  | .app (s := .prop) (.app (s := .prop) (.const ⟨"iff", 0⟩) p) q =>
      return (← formula ρ p).iff (← formula ρ q)
  | .app (s := .ind) (.app (s := .ind) (.const ⟨"eq", 0⟩) t) u =>
      return .equal (← term ρ t) (← term ρ u)
  | .app (s := .arrow .ind .prop) (.const ⟨"forall", 0⟩) (.lam _ p) =>
      return (← formula (bind ρ) p).all
  | .app (s := .arrow .ind .prop) (.const ⟨"exists", 0⟩) (.lam _ p) =>
      return (← formula (bind ρ) p).ex
  | .free x => some (.rel ⟨true, x⟩ Fin.elim0)
  | .const c => some (.rel ⟨false, c⟩ Fin.elim0)
  | .app (s := .ind) f a => do
      let (symbol, args) ← spine ρ f
      let a' ← term ρ a
      let args := args ++ [a']
      return .rel symbol args.get
  | _ => none


def readFormula (e : Expr) : Option (Pure.Formula language) := do
  let ⟨s, t⟩ ← normalized e
  match s, t with
  | .prop, t => formula (fun _ => none) t
  | _, _ => none

def readTerm (e : Expr) : Option (Pure.Term language) := do
  let ⟨s, t⟩ ← normalized e
  match s, t with
  | .ind, t =>
      (term (fun _ => none) t).map (FirstOrder.Language.Term.relabel (Sum.elim id Fin.elim0))
  | _, _ => none

theorem readFormula_eq {e f : Expr} (h : AlphaBetaEta e f) :
    readFormula e = readFormula f := by simp only [readFormula, normalized_eq h]

theorem readTerm_eq {e f : Expr} (h : AlphaBetaEta e f) :
    readTerm e = readTerm f := by simp only [readTerm, normalized_eq h]

@[simp] theorem readFormula_bot : readFormula Expr.bot = some ⊥ := by
  simp [readFormula, normalized, Expr.bot, interpretNamed, normalize, eval,
    quote, reflect, readback, formula, SConst.named]

@[simp] theorem readFormula_top : readFormula Expr.top = some ⊤ := by
  simp [readFormula, normalized, Expr.top, interpretNamed, normalize, eval,
    quote, reflect, readback, formula, SConst.named]

theorem readFormula_neg {p : Expr} (hp : isFormula p) :
    readFormula (Expr.neg p) = (readFormula p).map Language.BoundedFormula.not := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  simp [readFormula, normalized, Expr.neg, interpretNamed, hp', Packed.app,
    normalize, eval, quote, reflect, readback, formula]
  cases formula (fun _ => none) (eval p' ambient Depth.zero) <;> simp

theorem readFormula_and {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.and p q) = (do return (← readFormula p) ⊓ (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.and, interpretNamed, hp', hq', Packed.app,
    normalize, eval, quote, reflect, readback, formula]

theorem readFormula_or {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.or p q) = (do return (← readFormula p) ⊔ (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.or, interpretNamed, hp', hq', Packed.app,
    normalize, eval, quote, reflect, readback, formula]

theorem readFormula_imp {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.imp p q) =
      (do return (← readFormula p).imp (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.imp, interpretNamed, hp', hq', Packed.app,
    normalize, eval, quote, reflect, readback, formula]

theorem readFormula_iff {p q : Expr} (hp : isFormula p) (hq : isFormula q) :
    readFormula (Expr.iff p q) =
      (do return (← readFormula p).iff (← readFormula q)) := by
  obtain ⟨p', hp'⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨q', hq'⟩ := interpretNamed_sorted hq Names.free
  simp [readFormula, normalized, Expr.iff, interpretNamed, hp', hq', Packed.app,
    normalize, eval, quote, reflect, readback, formula]

/-- Readback is well-defined on A's formula classes, not chosen representatives. -/
def ofFormula (p : A.Formula) : Option (Pure.Formula language) :=
  Quotient.lift readFormula (fun _ _ h => readFormula_eq h) p.val

def ofTerm (t : A.Term) : Option (Pure.Term language) :=
  Quotient.lift readTerm (fun _ _ h => readTerm_eq h) t.val

@[simp] theorem ofFormula_ofExpr (p : Expr) (hp : isFormula p) :
    ofFormula (A.ofExpr p hp) = readFormula p := rfl

@[simp] theorem ofTerm_ofExpr (t : Expr) (ht : isTerm t) :
    ofTerm (A.ofExpr t ht) = readTerm t := rfl

end Lisa.SCLambdaToPure.Readback
