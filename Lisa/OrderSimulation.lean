import Lisa.Order

open Lisa Expr

/-! Relation inclusion transfers positive comparisons and their context predicates.
Negative answers are not transferred: discharge may retain different assumptions.
-/
namespace Subrelation

variable {source target : ExprRel}

theorem same (sim : Subrelation source target) {p q}
    (h : isSame source p q) : isSame target p q :=
  ⟨sim h.1, sim h.2⟩

theorem sequent (sim : Subrelation source target) {Γ Δ Γ' Δ'}
    (h : sequentLeq source Γ Δ Γ' Δ') : sequentLeq target Γ Δ Γ' Δ' :=
  sim h

theorem member (sim : Subrelation source target) {p Γ}
    (h : ordContains source p Γ) : ordContains target p Γ := by
  obtain ⟨q, hq, he⟩ := h
  exact ⟨q, hq, sim.same he⟩

theorem members (sim : Subrelation source target) {Γ Δ}
    (h : setLeq source Γ Δ) : setLeq target Γ Δ := by
  intro p hp
  obtain ⟨q, hq, he⟩ := h p hp
  exact ⟨q, hq, sim.same he⟩

theorem except (sim : Subrelation source target) {Γ Δ p}
    (h : containedExcept source Γ Δ p) : containedExcept target Γ Δ p := by
  intro q hq
  rcases h q hq with ⟨r, hr, he⟩ | he
  · exact Or.inl ⟨r, hr, sim.same he⟩
  · exact Or.inr (sim.same he)

theorem exceptEither (sim : Subrelation source target) {Γ Δ p q}
    (h : containedExceptEither source Γ Δ p q) :
    containedExceptEither target Γ Δ p q := by
  intro r hr
  rcases h r hr with h | h | h
  · exact Or.inl (sim.member h)
  · exact Or.inr (Or.inl (sim.same h))
  · exact Or.inr (Or.inr (sim.same h))

end Subrelation
