import Lisa.Orthologic.CutElimination
import Lisa.Orthologic.Orthogonal

namespace Lisa.Orthologic

namespace Calculus.Proof

/-- Interpret an absent position by any requested formula in the cut-free certificate. -/
theorem toOrthogonal {α : Type} {g d} (h : @Proof α false g d) :
    ∀ p q, (g = none ∨ g = some p) → (d = none ∨ d = some q) → Orthogonal p q := by
  induction h with
  | ax p =>
    intro r s hr hs
    simp only [reduceCtorEq, false_or, Option.some.injEq] at hr hs
    subst r
    subst s
    exact .ax p
  | bot d =>
    intro p q hp _
    simp only [reduceCtorEq, false_or, Option.some.injEq] at hp
    subst p
    exact .bot q
  | weaken h ih =>
    intro p q hp _
    exact ih p q hp (Or.inl rfl)
  | contract h ih =>
    intro p q hp _
    exact .weaken (ih p p hp hp)
  | meetLeft h ih =>
    intro p q hp hq
    simp only [reduceCtorEq, false_or, Option.some.injEq] at hp
    subst p
    exact .meetLeft (ih _ q (Or.inr rfl) hq)
  | meetRight h ih =>
    intro p q hp hq
    simp only [reduceCtorEq, false_or, Option.some.injEq] at hp
    subst p
    exact .meetRight (ih _ q (Or.inr rfl) hq)
  | join h k ih ik =>
    intro p q hp hq
    simp only [reduceCtorEq, false_or, Option.some.injEq] at hp
    subst p
    exact .join (ih _ q (Or.inr rfl) hq) (ik _ q (Or.inr rfl) hq)
  | swap h ih =>
    intro p q hp hq
    exact .symm (ih q p hq hp)
  | cut h _ _ _ _ => cases h

end Calculus.Proof

namespace Orthogonal

/-- Replay the compact search certificate in the two-position calculus. -/
theorem toProof {α : Type} {p q : Nnf α} (h : Orthogonal p q) :
    Nonempty (Calculus.Proof false (some p) (some q)) := by
  induction h with
  | ax p => exact ⟨.ax p⟩
  | bot p => exact ⟨.bot _⟩
  | symm h ih => exact ih.map Calculus.Proof.swap
  | meetLeft h ih => exact ih.map Calculus.Proof.meetLeft
  | meetRight h ih => exact ih.map Calculus.Proof.meetRight
  | join h k ih ik =>
    obtain ⟨h'⟩ := ih
    obtain ⟨k'⟩ := ik
    exact ⟨.join h' k'⟩
  | weaken h ih => exact ih.map (fun h' => .weaken (.contract h'))

theorem iff_cutFree {α : Type} (p q : Nnf α) :
    Orthogonal p q ↔ Nonempty (Calculus.Proof false (some p) (some q)) := by
  refine ⟨toProof, ?_⟩
  rintro ⟨h⟩
  exact h.toOrthogonal p q (Or.inr rfl) (Or.inr rfl)

/-- Derive every universally valid orthogonality statement in the search certificate type. -/
theorem complete {α : Type} (p q : Nnf α)
    (h : ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ (q.eval v)ᶜ) :
    Orthogonal p q := by
  obtain ⟨h'⟩ := Calculus.complete_cutFree p q.compl (by simpa using h)
  apply (iff_cutFree p q).mpr
  simpa only [Nnf.compl_compl] using (show Nonempty _ from ⟨h'⟩)

theorem iff_valid {α : Type} (p q : Nnf α) : Orthogonal p q ↔
    ∀ (L : Type) [Ortholattice L] (v : α → L), p.eval v ≤ (q.eval v)ᶜ :=
  ⟨fun h _ _ v => h.sound v, complete p q⟩

end Orthogonal

end Lisa.Orthologic
