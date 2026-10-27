import Lisa.Orthologic.Basic

/-! Derive orthocomplement laws from the ortholattice interface. -/

namespace Ortholattice

variable {L : Type} [Ortholattice L]

@[simp] theorem compl_compl (a : L) : aᶜᶜ = a := compl_involutive a

theorem compl_le_compl_iff (a b : L) : aᶜ ≤ bᶜ ↔ b ≤ a := by
  constructor
  · intro h
    simpa using compl_antitone h
  · intro h
    exact compl_antitone h

@[simp] theorem compl_top : (⊤ : L)ᶜ = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← compl_compl (⊥ : L)]
  exact compl_antitone le_top

@[simp] theorem compl_bot : (⊥ : L)ᶜ = ⊤ := by
  rw [← compl_top, compl_compl]

@[simp] theorem compl_sup (a b : L) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  apply le_antisymm
  · exact le_inf (compl_antitone le_sup_left) (compl_antitone le_sup_right)
  · apply (compl_le_compl_iff _ _).mp
    simp only [compl_compl]
    apply sup_le
    · simpa using (compl_antitone (inf_le_left : aᶜ ⊓ bᶜ ≤ aᶜ))
    · simpa using (compl_antitone (inf_le_right : aᶜ ⊓ bᶜ ≤ bᶜ))

@[simp] theorem compl_inf (a b : L) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by
  apply compl_involutive.injective
  simp

@[simp] theorem inf_compl (a : L) : a ⊓ aᶜ = ⊥ := by
  rw [← compl_top, ← sup_compl a, compl_sup, compl_compl, inf_comm]

theorem orth_comm (a b : L) : a ≤ bᶜ ↔ b ≤ aᶜ := by
  constructor <;> intro h <;> simpa using compl_antitone h

theorem self_orth_iff (a : L) : a ≤ aᶜ ↔ a = ⊥ := by
  constructor
  · intro h
    exact le_antisymm (by simpa using (le_inf le_rfl h : a ≤ a ⊓ aᶜ)) bot_le
  · rintro rfl
    exact bot_le

end Ortholattice
