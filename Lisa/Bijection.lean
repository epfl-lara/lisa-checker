import Lisa.Syntax
import Lisa.Standard
import Lisa.Weakened

open Lisa

def fwdEmbed {leq Γ Δ} (href : Reflexive leq) :
    Standard.ProofTree leq Γ Δ ->
    Weakened.ProofTree leq Γ Δ := sorry

def bwdEmbed  {leq Γ Δ} (href : Reflexive leq) :
    Weakened.ProofTree leq Γ Δ ->
    Standard.ProofTree leq Γ Δ := sorry

theorem standard_eq_weakened (leq : Order) (Γ Δ : Finset Expr) (href : Reflexive leq) :
    Nonempty (Standard.ProofTree leq Γ Δ) ↔
    Nonempty (Weakened.ProofTree leq Γ Δ) := by
  constructor <;> intro ⟨pf⟩
  · exact ⟨fwdEmbed href pf⟩
  · exact ⟨bwdEmbed href pf⟩
