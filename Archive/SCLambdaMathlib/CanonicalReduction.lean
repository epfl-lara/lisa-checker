import Lisa.SCLambdaToPure.BoundaryNames
import Lisa.SCLambdaToPure.PureToA

/-! The concrete reduction specialized to the first-order boundary in the paper.
The hypotheses below concern only the concluding sequent. Intermediate formulas
in its A proof may contain arbitrary higher-order symbols.
-/

namespace Lisa.SCLambdaToPure

/-- The paper's restriction before adding description operators. Higher-order
bound variables and redexes are allowed; free variables have ground sorts. -/
def FirstOrderBoundary (p : Expr) : Prop :=
  FirstOrderShape.ConstantsInLanguage p ∧
    ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop

namespace Translation

theorem canonical_read_total {p : Expr} (hp : isFormula p) (hb : FirstOrderBoundary p) :
    (Readback.readFormula p).isSome := by
  rw [← readFormula_of_firstOrder hp hb.1 hb.2]
  exact readFormula_total hp

/-- Read the ordinary αβη canonical form. No grounding changes this boundary. -/
def canonicalFormula (p : Expr) (hp : isFormula p) (hb : FirstOrderBoundary p) :
    Pure.Formula Readback.language :=
  (Readback.readFormula p).get (canonical_read_total hp hb)

theorem formula_eq_canonical (p : Expr) (hp : isFormula p) (hb : FirstOrderBoundary p) :
    formula (A.ofExpr p hp) = canonicalFormula p hp hb := by
  apply Option.some.inj
  rw [some_formula, readFormula_of_firstOrder hp hb.1 hb.2]
  exact (Option.some_get _).symm

noncomputable def canonicalContext (Γ : Finset Expr) (hΓ : isFSet Γ)
    (hb : ∀ p ∈ Γ, FirstOrderBoundary p) : Pure.Context Readback.language :=
  Γ.attach.image (fun p => canonicalFormula p.val (hΓ p.val p.property) (hb p.val p.property))

theorem context_eq_canonical (Γ : Finset Expr) (hΓ : isFSet Γ)
    (hb : ∀ p ∈ Γ, FirstOrderBoundary p) :
    context (A.context Γ hΓ) = canonicalContext Γ hΓ hb := by
  classical
  simp only [context, A.context, canonicalContext, Finset.image_image]
  apply Finset.image_congr
  intro p _
  exact formula_eq_canonical p.val (hΓ p.val p.property) (hb p.val p.property)

/-- The forward direction of `sclamA_conservative`: translate the whole proof,
not merely the formulas at its conclusion. This theorem assumes no property of
the proof's intermediate formulas and no unproved interpretation laws. -/
noncomputable def toPureCanonical {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p)
    (d : A.ProofTree ∅ (A.context Γ hΓ) (A.context Δ hΔ)) :
    Pure.ProofTree ∅ (canonicalContext Γ hΓ hbΓ) (canonicalContext Δ hΔ hbΔ) := by
  simpa only [context_eq_canonical Γ hΓ hbΓ, context_eq_canonical Δ hΔ hbΔ] using toPure d

theorem provable_toPureCanonical {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p)
    (h : A.Provable ∅ (A.context Γ hΓ) (A.context Δ hΔ)) :
    Pure.Provable ∅ (canonicalContext Γ hΓ hbΓ) (canonicalContext Δ hΔ hbΔ) := by
  obtain ⟨d⟩ := h
  exact ⟨toPureCanonical hΓ hΔ hbΓ hbΔ d⟩

end Translation
end Lisa.SCLambdaToPure
