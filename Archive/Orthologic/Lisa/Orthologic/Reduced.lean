import Lisa.Orthologic.LatticeContainment
import Lisa.Orthologic.Orthogonal

/-!
Isolate the invariant needed to replace orthologic search by lattice comparison.
Every subterm must contract or expand by lattice rules whenever it lies below
its complement or above it. No canonical operand order is required.
-/

namespace Lisa.Orthologic.Nnf

variable {α : Type}

/-- Require lattice-detectable contradictions and tautologies at every subterm. -/
def Reduced : Nnf α → Prop
  | .lit .. | .bot | .top => True
  | .meet p q => Reduced p ∧ Reduced q ∧
      (LatticeLe (.meet p q) (Nnf.meet p q).compl → LatticeLe (.meet p q) .bot)
  | .join p q => Reduced p ∧ Reduced q ∧
      (LatticeLe (Nnf.join p q).compl (.join p q) → LatticeLe .top (.join p q))

namespace Reduced

/-- Contract self-orthogonality using lattice containment alone. -/
theorem contract {p : Nnf α} (hp : p.Reduced) (h : LatticeLe p p.compl) :
    LatticeLe p .bot := by
  induction p with
  | lit a s => cases s <;> cases h
  | bot => exact .refl _
  | top => cases h
  | meet p q _ _ => exact hp.2.2 h
  | join p q ih ik =>
      have h' := h.of_join
      exact .join (ih hp.1 h'.1.to_meet.1) (ik hp.2.1 h'.2.to_meet.2)

/-- Expand a term above its complement using lattice containment alone. -/
theorem expand {p : Nnf α} (hp : p.Reduced) (h : LatticeLe p.compl p) :
    LatticeLe .top p := by
  induction p with
  | lit a s => cases s <;> cases h
  | bot => cases h
  | top => exact .refl _
  | meet p q ih ik =>
      have h' := h.of_join
      exact .meet (ih hp.1 h'.1.to_meet.1) (ik hp.2.1 h'.2.to_meet.2)
  | join p q _ _ => exact hp.2.2 h

theorem compl {p : Nnf α} (hp : p.Reduced) : p.compl.Reduced := by
  induction p with
  | lit a s => trivial
  | bot => trivial
  | top => trivial
  | meet p q ih ik =>
      refine ⟨ih hp.1, ik hp.2.1, ?_⟩
      intro h
      have hc := (contract hp (by simpa only [Nnf.compl, compl_compl] using h)).compl
      exact hc
  | join p q ih ik =>
      refine ⟨ih hp.1, ik hp.2.1, ?_⟩
      intro h
      have hc := (expand hp (by simpa only [Nnf.compl, compl_compl] using h)).compl
      exact hc

end Reduced
end Nnf

/-- On reduced operands, orthologic certificates need no contraction search. -/
theorem Orthogonal.lattice_of_reduced {α : Type} {p q : Nnf α}
    (h : Orthogonal p q) (hp : p.Reduced) (hq : q.Reduced) :
    Nnf.LatticeLe p q.compl := by
  induction h with
  | ax p => simpa using Nnf.LatticeLe.refl p
  | bot p => exact .bot _
  | symm h ih => simpa using (ih hq hp).compl
  | meetLeft h ih => exact .projectLeft (ih hp.1 hq)
  | meetRight h ih => exact .projectRight (ih hp.2.1 hq)
  | join h k ih ik => exact .join (ih hp.1 hq) (ik hp.2.1 hq)
  | weaken h ih => exact (hp.contract (ih hp hp)).trans (.bot _)

end Lisa.Orthologic
