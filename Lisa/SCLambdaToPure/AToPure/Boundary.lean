import Lisa.SCLambdaToPure.AToPure.Translation

/-! The concluding formulas to which the equivalence applies, and their
canonical first-order translation. Epsilon remains in the first-order language.
Intermediate formulas of a derivation need not satisfy this boundary. -/
namespace Lisa.SCLambdaToPure

/-- First-order constants, logical constants (including epsilon), and free
individual/proposition variables. Higher-order bound variables and redexes are
allowed: canonicalization removes them. -/
def FirstOrderBoundary (p : Expr) : Prop :=
  FirstOrderShape.ConstantsInLanguage p ∧
    ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop

namespace Readback

/-- Canonical first-order readback. The default is unreachable on sorted
boundary formulas, as proved by `canonical_spec`. -/
def canonical (p : Expr) : Pure.Formula Readback.language :=
  (readFormula p).getD .bot

noncomputable def canonicalContext (Γ : Finset Expr) : Pure.Context Readback.language :=
  Γ.image canonical

theorem canonical_spec {p : Expr} (hp : isFormula p) (hb : FirstOrderBoundary p) :
    readFormula p = some (canonical p) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (readFormula_isSome hp hb.1 hb.2)
  simp [canonical, hq]

theorem grounding_formula {p : Expr} (hp : isFormula p) (hb : FirstOrderBoundary p) :
    Syntactic.Assignment.grounding.formula p = canonical p := by
  obtain ⟨e, he⟩ := Lambda.interpretNamed_sorted hp Lambda.Names.free
  let a : Syntactic.ScopedExpr prop :=
    ⟨e, FirstOrderShape.inLanguage_of_interpretNamed he hb.1 hb.2, Lambda.subst_of_interpretNamed he⟩
  have hf : Syntactic.Assignment.grounding.expression p hp = a := by
    rw [Syntactic.Assignment.expression_of_named _ p hp he]
    exact Syntactic.Assignment.grounding_apply a
  rw [Syntactic.Assignment.formula_of_sorted _ p hp, hf]
  have hr : readFormula p = some a.readFormula := by
    simpa [readFormula, Readback.normalized, he, a] using a.readFormula_spec
  exact Option.some.inj (hr.symm.trans (canonical_spec hp hb))

theorem grounding_context {Γ : Finset Expr} (hΓ : isFSet Γ)
    (hb : ∀ p ∈ Γ, FirstOrderBoundary p) :
    Syntactic.Assignment.grounding.context Γ = canonicalContext Γ := by
  apply Finset.image_congr
  intro p hp
  exact grounding_formula (hΓ p hp) (hb p hp)

end Readback

end Lisa.SCLambdaToPure
