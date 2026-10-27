import Lisa.SCLambdaToPure.Translation
import Lisa.SCLambdaToPure.ReadbackBinding

/-! The concrete translation preserves individual quantifiers. -/

namespace Lisa.SCLambdaToPure.Translation

open FirstOrder Lambda

theorem ground_abstract (x : Identifier) (e : Term s) :
    Grounding.ground ((Replacement.abstract ⟨x, ind⟩).apply e) =
      (Replacement.abstract ⟨x, ind⟩).apply (Grounding.ground e) := by
  rw [← Readback.abstractAt_zero]
  apply Replacement.ground_apply
  · intros; rfl
  · intro y; simp only [Readback.abstractAt]; split <;> rfl
  · intro s hs y; exact (Readback.abstractAt_heads x 0).free s hs y
  · intros; rfl

private theorem normalize_all (x : Identifier) (e : Term prop) (hc : ∀ σ, e.subst σ = e) :
    normalize (.app (.const ⟨"forall", 0⟩)
      (.lam ind ((Replacement.abstract ⟨x, ind⟩).apply (Grounding.ground e))) : Term prop) =
    .app (.const ⟨"forall", 0⟩)
      (.lam ind ((Replacement.abstract ⟨x, ind⟩).apply (normalize (Grounding.ground e)))) := by
  rw [normalize_eq_of_equiv (Lambda.Equiv.app (Lambda.Equiv.refl _) (Lambda.Equiv.lam
    ((Replacement.abstract ⟨x, ind⟩).equiv (normalize_sound (Grounding.ground e)))))]
  exact FirstOrderShape.normalize_formula_eq (.all
    (Replacement.formula (Replacement.abstract_firstOrder ⟨x, ind⟩ rfl)
      (Grounding.normalize_ground_formula hc)))

private theorem normalize_ex (x : Identifier) (e : Term prop) (hc : ∀ σ, e.subst σ = e) :
    normalize (.app (.const ⟨"exists", 0⟩)
      (.lam ind ((Replacement.abstract ⟨x, ind⟩).apply (Grounding.ground e))) : Term prop) =
    .app (.const ⟨"exists", 0⟩)
      (.lam ind ((Replacement.abstract ⟨x, ind⟩).apply (normalize (Grounding.ground e)))) := by
  rw [normalize_eq_of_equiv (Lambda.Equiv.app (Lambda.Equiv.refl _) (Lambda.Equiv.lam
    ((Replacement.abstract ⟨x, ind⟩).equiv (normalize_sound (Grounding.ground e)))))]
  exact FirstOrderShape.normalize_formula_eq (.ex
    (Replacement.formula (Replacement.abstract_firstOrder ⟨x, ind⟩ rfl)
      (Grounding.normalize_ground_formula hc)))

theorem formula_all (x : SVar) (p : Expr) (hx : x.sort = ind) (hp : isFormula p) :
    formula (A.ofExpr (Expr.forall_ x p) (isFormula_forall hx hp)) =
      Pure.forall_ (Readback.variableCode x.id) (formula (A.ofExpr p hp)) := by
  obtain ⟨x, s⟩ := x
  cases hx
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hread := (some_formula p hp).symm
  simp only [readFormula, normalized, he, Option.map_some] at hread
  have hab := Readback.formula_abstract hread x
  apply formula_eq_of_read
  simp [readFormula, normalized, Expr.forall_, interpretNamed, Replacement.interpretNamed_bind,
    he, Packed.lam, Packed.app, Replacement.packed, ground_abstract,
    Grounding.ground_const FirstOrderShape.Constant.all,
    normalize_all x e (subst_of_interpretNamed he), Readback.formula, hab, Pure.forall_]

theorem formula_ex (x : SVar) (p : Expr) (hx : x.sort = ind) (hp : isFormula p) :
    formula (A.ofExpr (Expr.exists_ x p) (isFormula_exists hx hp)) =
      Pure.exists_ (Readback.variableCode x.id) (formula (A.ofExpr p hp)) := by
  obtain ⟨x, s⟩ := x
  cases hx
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hread := (some_formula p hp).symm
  simp only [readFormula, normalized, he, Option.map_some] at hread
  have hab := Readback.formula_abstract hread x
  apply formula_eq_of_read
  simp [readFormula, normalized, Expr.exists_, interpretNamed, Replacement.interpretNamed_bind,
    he, Packed.lam, Packed.app, Replacement.packed, ground_abstract,
    Grounding.ground_const FirstOrderShape.Constant.ex,
    normalize_ex x e (subst_of_interpretNamed he), Readback.formula, hab, Pure.exists_]

end Lisa.SCLambdaToPure.Translation
