import Lisa.Orthologic.Formula

/-! Use a compact cut-free certificate independently of any search algorithm. -/

namespace Lisa.Orthologic

/-- Derive orthogonality without cut or a distributivity rule. -/
inductive Orthogonal {α : Type} : Nnf α → Nnf α → Prop
  | ax (p) : Orthogonal p p.compl
  | bot (p) : Orthogonal .bot p
  | symm {p q} : Orthogonal p q → Orthogonal q p
  | meetLeft {p q r} : Orthogonal p r → Orthogonal (.meet p q) r
  | meetRight {p q r} : Orthogonal q r → Orthogonal (.meet p q) r
  | join {p q r} : Orthogonal p r → Orthogonal q r → Orthogonal (.join p q) r
  | weaken {p q} : Orthogonal p p → Orthogonal p q

/-- Interpret a cut-free derivation in any ortholattice. -/
theorem Orthogonal.sound {α L : Type} [Ortholattice L] {p q : Nnf α}
    (h : Orthogonal p q) (v : α → L) : p.eval v ≤ (q.eval v)ᶜ := by
  induction h with
  | ax p => simp
  | bot p => exact bot_le
  | symm _ ih => exact (Ortholattice.orth_comm _ _).mp ih
  | meetLeft _ ih => exact le_trans inf_le_left ih
  | meetRight _ ih => exact le_trans inf_le_right ih
  | join _ _ ih₁ ih₂ => exact sup_le ih₁ ih₂
  | weaken _ ih =>
      have h := (Ortholattice.self_orth_iff _).mp ih
      rw [h]
      exact bot_le

end Lisa.Orthologic
