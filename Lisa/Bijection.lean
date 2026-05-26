import Lisa.Syntax
import Lisa.Standard
import Lisa.Weakened

open Lisa

def fwdEmbed {leq Γ Δ} :
    Standard.ProofTree leq Γ Δ ->
    Weakened.ProofTree leq Γ Δ := sorry

def bwdEmbed  {leq Γ Δ} :
    Weakened.ProofTree leq Γ Δ ->
    Standard.ProofTree leq Γ Δ := sorry

theorem standard_eq_weakened :
  ∀ leq Γ Δ,
    Nonempty (Standard.ProofTree leq Γ Δ) ↔
    Nonempty (Weakened.ProofTree leq Γ Δ) := by
  intros leq Γ Δ
  constructor <;> intro ⟨pf⟩
  · exact ⟨fwdEmbed pf⟩
  · exact ⟨bwdEmbed pf⟩
