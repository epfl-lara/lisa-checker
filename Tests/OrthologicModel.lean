import Lisa.Orthologic.Formula
import Mathlib.Tactic.DeriveFintype

/-! Use a nondistributive ortholattice to separate OL from Boolean logic. -/

namespace OrthologicModel

inductive Diamond where
  | bot | top | a | a' | b | b'
  deriving DecidableEq, Fintype, Repr

namespace Diamond

def ordered (x y : Diamond) : Prop := x = .bot ∨ y = .top ∨ x = y

instance : DecidableRel ordered := fun x y =>
  inferInstanceAs (Decidable (x = .bot ∨ y = .top ∨ x = y))

instance : PartialOrder Diamond where
  le := ordered
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := Diamond) (· ≤ ·) :=
  fun x y => inferInstanceAs (Decidable (ordered x y))

def meet : Diamond → Diamond → Diamond
  | .bot, _ | _, .bot => .bot
  | .top, y => y
  | x, .top => x
  | x, y => if x = y then x else .bot

def join : Diamond → Diamond → Diamond
  | .top, _ | _, .top => .top
  | .bot, y => y
  | x, .bot => x
  | x, y => if x = y then x else .top

instance : Lattice Diamond where
  inf := meet
  sup := join
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : BoundedOrder Diamond where
  top := .top
  bot := .bot
  le_top := by decide
  bot_le := by decide

def complement : Diamond → Diamond
  | .bot => .top
  | .top => .bot
  | .a => .a'
  | .a' => .a
  | .b => .b'
  | .b' => .b

instance : Compl Diamond := ⟨complement⟩

instance : Ortholattice Diamond where
  compl_antitone := by decide
  compl_involutive := by intro x; cases x <;> rfl
  sup_compl := by decide

example : (.a : Diamond) ⊓ (.b ⊔ .b') ≠ (.a ⊓ .b) ⊔ (.a ⊓ .b') := by decide

end Diamond

open Lisa.Orthologic

def valuation : Nat → Diamond
  | 0 => .a
  | 1 => .b
  | _ => .b'

def lhs : Nnf Nat := .meet (.lit 0 false) (.join (.lit 1 false) (.lit 2 false))
def rhs : Nnf Nat := .join (.meet (.lit 0 false) (.lit 1 false))
  (.meet (.lit 0 false) (.lit 2 false))

theorem not_distributive : ¬ lhs.eval valuation ≤ rhs.eval valuation := by decide

end OrthologicModel
