import Lisa.SCLambdaToPure.FormulaRoundtrip

/-! System A is conservative on the first-order boundary. The forward proof
grounds intermediate symbols and canonicalizes every formula; the reverse proof
interprets a pure derivation and uses cuts to recover the original boundary.
-/

namespace Lisa.SCLambdaToPure

namespace A.Provable

private theorem replaceLeftAux {T : A.Theory} (Γ Γ₀ Δ : A.Context)
    (h : ∀ p ∈ Γ, A.Provable T Γ₀ {p}) (d : A.Provable T (Γ ∪ Γ₀) Δ) : A.Provable T Γ₀ Δ := by
  induction Γ using Finset.induction_on with
  | empty => simpa using d
  | @insert p Γ hp ih =>
      obtain ⟨dp⟩ := h p (Finset.mem_insert_self _ _)
      obtain ⟨d⟩ := d
      apply ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
      refine ⟨?_⟩
      simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using
        A.ProofTree.cut (Γ := Γ₀) (Δ := ∅) (Γ₁ := Γ ∪ Γ₀) (Δ₁ := Δ) p
          (by simpa using dp) (by simpa using d)

theorem replaceLeft {T : A.Theory} {Γ Γ₀ Δ : A.Context}
    (d : A.Provable T Γ Δ) (h : ∀ p ∈ Γ, A.Provable T Γ₀ {p}) : A.Provable T Γ₀ Δ := by
  obtain ⟨d⟩ := d
  exact replaceLeftAux Γ Γ₀ Δ h ⟨d.weakening (by intro p hp; exact Finset.mem_union_left _ hp) (by simp)⟩

private theorem replaceRightAux {T : A.Theory} (Δ Δ₀ Γ : A.Context)
    (h : ∀ p ∈ Δ, A.Provable T {p} Δ₀) (d : A.Provable T Γ (Δ ∪ Δ₀)) : A.Provable T Γ Δ₀ := by
  induction Δ using Finset.induction_on with
  | empty => simpa using d
  | @insert p Δ hp ih =>
      obtain ⟨dp⟩ := h p (Finset.mem_insert_self _ _)
      obtain ⟨d⟩ := d
      apply ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
      refine ⟨?_⟩
      simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using
        A.ProofTree.cut (Γ := Γ) (Δ := Δ ∪ Δ₀) (Γ₁ := ∅) (Δ₁ := Δ₀) p
          (by simpa using d) (by simpa using dp)

theorem replaceRight {T : A.Theory} {Γ Δ Δ₀ : A.Context}
    (d : A.Provable T Γ Δ) (h : ∀ p ∈ Δ, A.Provable T {p} Δ₀) : A.Provable T Γ Δ₀ := by
  obtain ⟨d⟩ := d
  exact replaceRightAux Δ Δ₀ Γ h ⟨d.weakening (by simp) (by intro p hp; exact Finset.mem_union_left _ hp)⟩

end A.Provable

namespace Embedding

theorem sharedNames (Γ : A.Context) (hΓ : ∀ p ∈ Γ, Roundtrip p) :
    ∃ η : Nat → Identifier, Function.Injective η ∧
      ∀ p ∈ Γ, Nonempty (Related η p (Translation.formula p)) := by
  classical
  let support (p : A.Formula) : Finset Identifier :=
    if hp : p ∈ Γ then Classical.choose (hΓ p hp) else ∅
  obtain ⟨η, hη, hn⟩ := boundaryNames (Γ.biUnion support)
  refine ⟨η, hη, fun p hp => ?_⟩
  apply Classical.choose_spec (hΓ p hp) η hη
  intro x hx
  apply hn
  apply Finset.mem_biUnion.mpr
  exact ⟨p, hp, by simpa only [support, dif_pos hp] using hx⟩

/-- Once each concluding formula is first-order, the reverse interpretation
can be restated back to that very sequent. -/
theorem provable_of_toPure {Γ Δ : A.Context}
    (hΓ : ∀ p ∈ Γ, Roundtrip p) (hΔ : ∀ p ∈ Δ, Roundtrip p)
    (h : Pure.Provable ∅ (Translation.context Γ) (Translation.context Δ)) :
    A.Provable ∅ Γ Δ := by
  obtain ⟨η, hη, hn⟩ := sharedNames (Γ ∪ Δ) (fun p hp =>
    (Finset.mem_union.mp hp).elim (hΓ p) (hΔ p))
  obtain ⟨d⟩ := h
  have hd : A.Provable ∅ (context η (Translation.context Γ)) (context η (Translation.context Δ)) :=
    ⟨toA η hη d⟩
  refine A.Provable.replaceRight (A.Provable.replaceLeft hd ?_) ?_
  · intro q hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨r⟩ := hn p (Finset.mem_union_left _ hp)
    exact ⟨r.forward.weakening (Finset.singleton_subset_iff.mpr hp) (by simp)⟩
  · intro q hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨r⟩ := hn p (Finset.mem_union_right _ hp)
    exact ⟨r.backward.weakening (by simp) (Finset.singleton_subset_iff.mpr hp)⟩

end Embedding

/-- The equivalence from `sclamA_conservative` in the paper.

The boundary may contain higher-order binders and redexes, provided its free
variables have ground sorts and its constants are first-order. There is no
restriction on intermediate formulas in the A proof. Assumptions are represented
by the antecedent; the theorem does not extend a theory's axiom schemas.
-/
theorem a_iff_pure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    A.Provable ∅ (A.context Γ hΓ) (A.context Δ hΔ) ↔
      Pure.Provable ∅ (Translation.canonicalContext Γ hΓ hbΓ)
        (Translation.canonicalContext Δ hΔ hbΔ) := by
  constructor
  · exact Translation.provable_toPureCanonical hΓ hΔ hbΓ hbΔ
  · intro h
    rw [← Translation.context_eq_canonical Γ hΓ hbΓ,
      ← Translation.context_eq_canonical Δ hΔ hbΔ] at h
    apply Embedding.provable_of_toPure (h := h)
    · intro p hp
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hp
      exact Embedding.firstOrder_roundtrip (hΓ e.val e.property) (hbΓ e.val e.property)
    · intro p hp
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hp
      exact Embedding.firstOrder_roundtrip (hΔ e.val e.property) (hbΔ e.val e.property)

end Lisa.SCLambdaToPure

