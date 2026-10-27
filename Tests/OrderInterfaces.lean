import Lisa.OrderedWeakened
import Lisa.ImportedWeakened

/-! The generic proof systems accept equality without importing orthologic. -/
open Lisa Expr

run_cmd do
  let env ← Lean.getEnv
  for name in [`Ortholattice, `Lisa.Orthologic.Interpretation,
      `Lisa.Orthologic.Calculus.Free, `OrderReduction, `CheckerOrder, `SequentEncoding] do
    if env.contains name then
      throwError "The proof-system interface imports {name}"

namespace DiagonalOrderTests

local instance : RelationCongruence (Eq : ExprRel) where
  imp_congr hp hq := by rcases hp with ⟨rfl, _⟩; rcases hq with ⟨rfl, _⟩; exact ⟨rfl, rfl⟩
  eq_congr _ _ _ _ hs ht := by
    rcases hs with ⟨rfl, _⟩; rcases ht with ⟨rfl, _⟩; exact ⟨rfl, rfl⟩

local instance : ProofOrder (Eq : ExprRel) := ProofOrder.of _

-- The correspondence holds even though equality has none of the orthologic laws.
example (Γ Δ : Finset Expr) :
    Nonempty (Ordered.ProofTree Eq Γ Δ) ↔ Nonempty (Weakened.ProofTree Eq Γ Δ) :=
  ordered_eq_weakened Eq Γ Δ

example {Γ Δ ss} (imports : ∀ s ∈ ss, Nonempty (Weakened.ProofTree Eq s.1 s.2)) :
    Nonempty (Imported.ProofTree Eq Γ Δ ss) ↔ Nonempty (Weakened.ProofTree Eq Γ Δ) :=
  Imported.withAssumptions_iff imports

example (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
    Nonempty (Ordered.ProofTree Eq {p, q} {p}) := by
  apply Nonempty.intro
  exact .weakening (by simpa [isFSet] using hp) (by simpa [isFSet] using hp)
    (by simpa [isFSet] using And.intro hp hq) (by simpa [isFSet] using hp) (.hypothesis p hp)
    (by simp) (by rfl)

end DiagonalOrderTests
