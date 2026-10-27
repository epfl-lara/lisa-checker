import Lisa.Orthologic.Cached
import Lisa.Orthologic.ExpressionSoundness

/-! The cached pipeline inherits soundness in Ordered αβη by exact agreement.
No new reference relation or assumption about successful comparisons is needed. -/

namespace Lisa.Orthologic.Cached

theorem normalize_sound (hp : p.hasSort s) (h : normalize p config = some q) :
    ContextEq s p q :=
  Orthologic.normalize_sound hp (by simpa only [normalize_eq] using h)

theorem isSame_sound (h : isSame p q config = some true) :
    ∃ s, p.hasSort s ∧ q.hasSort s ∧ ContextEq s p q :=
  Orthologic.isSame_sound (by simpa only [isSame_eq] using h)

theorem isSame_formula_sound (hp : isFormula p) (h : isSame p q config = some true) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) ∧
      Nonempty (Ordered.AlphaBetaEtaProof {q} {p}) :=
  Orthologic.isSame_formula_sound hp (by simpa only [isSame_eq] using h)

theorem isImplying_sound (h : isImplying p q config = some true) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) :=
  Orthologic.isImplying_sound (by simpa only [isImplying_eq] using h)

end Lisa.Orthologic.Cached
