import Lisa.Order

open Lisa Expr

/-- Transfer positive comparisons and exact reduced matches to another order.

No negative comparison is transferred. In particular, different discharge
filters may retain different assumptions; resolution must follow the source
derivation's actual assumptions.
-/
structure OrderSimulation (source target : Order)
    [OrderReduction source] [OrderReduction target] : Prop where
  compare : ∀ {p q}, source p q → target p q
  reduced : ∀ {p q}, reducedSame source p q → reducedSame target p q

namespace OrderSimulation

variable {source target : Order} [OrderReduction source] [OrderReduction target]

def refl (order : Order) [OrderReduction order] : OrderSimulation order order :=
  ⟨fun h => h, fun h => h⟩

theorem same (sim : OrderSimulation source target) {p q}
    (h : isSame source p q) : isSame target p q :=
  ⟨sim.compare h.1, sim.compare h.2⟩

theorem sequent (sim : OrderSimulation source target) {Γ Δ Γ' Δ'}
    (h : sequentLeq source Γ Δ Γ' Δ') : sequentLeq target Γ Δ Γ' Δ' :=
  sim.compare h

theorem member (sim : OrderSimulation source target) {p Γ}
    (h : ordContains source p Γ) : ordContains target p Γ := by
  obtain ⟨q, hq, he⟩ := h
  exact ⟨q, hq, sim.same he⟩

theorem members (sim : OrderSimulation source target) {Γ Δ}
    (h : setLeq source Γ Δ) : setLeq target Γ Δ := by
  intro p hp
  obtain ⟨q, hq, he⟩ := h p hp
  exact ⟨q, hq, sim.same he⟩

theorem reducedSubset (sim : OrderSimulation source target) {Γ Δ}
    (h : _root_.reducedSubset source Γ Δ) : _root_.reducedSubset target Γ Δ := by
  intro p hp
  obtain ⟨q, hq, he⟩ := h p hp
  exact ⟨q, hq, sim.reduced he⟩

theorem except (sim : OrderSimulation source target) {Γ Δ p}
    (h : containedExcept source Γ Δ p) : containedExcept target Γ Δ p := by
  intro q hq
  rcases h q hq with ⟨r, hr, he⟩ | he
  · exact Or.inl ⟨r, hr, sim.reduced he⟩
  · exact Or.inr (sim.same he)

theorem exceptEither (sim : OrderSimulation source target) {Γ Δ p q}
    (h : containedExceptEither source Γ Δ p q) :
    containedExceptEither target Γ Δ p q := by
  intro r hr
  rcases h r hr with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (sim.same h))
  · exact Or.inr (Or.inr (sim.same h))

end OrderSimulation
