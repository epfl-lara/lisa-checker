import Mathlib.Order.BooleanAlgebra.Defs

/-! Specify an ortholattice independently of expression syntax and proof systems. -/

/-- Equip a bounded lattice with an order-reversing orthocomplement. -/
class Ortholattice (α : Type) extends Lattice α, BoundedOrder α, Compl α where
  compl_antitone : Antitone (compl : α → α)
  compl_involutive : Function.Involutive (compl : α → α)
  sup_compl : ∀ a : α, a ⊔ aᶜ = ⊤
