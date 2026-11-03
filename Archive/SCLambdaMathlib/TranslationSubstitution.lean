import Lisa.SCLambdaToPure.TranslationBinding
import Lisa.SCLambdaToPure.ReadbackSubstitution
import Lisa.Lambda.NamedSubstitution

/-! Individual substitution commutes with the concrete translation. -/

namespace Lisa.SCLambdaToPure

open FirstOrder Lambda

private theorem equiv_instantiate {b c : Term s} {a d : Term t}
    (hb : Lambda.Equiv b c) (ha : Lambda.Equiv a d) :
    Lambda.Equiv (b.instantiate a) (c.instantiate d) :=
  (Lambda.Equiv.beta b a).symm.trans
    ((Lambda.Equiv.app (Lambda.Equiv.lam hb) ha).trans (Lambda.Equiv.beta c d))

namespace Translation

private theorem normalize_substitute (x : Identifier) (e : Term prop) (a : Term ind)
    (he : ∀ σ, e.subst σ = e) (ha : ∀ σ, a.subst σ = a) :
    normalize (Grounding.ground (((Replacement.abstract ⟨x, ind⟩).apply e).instantiate a)) =
      (Replacement.single ⟨x, ind⟩ (normalize (Grounding.ground a))).apply
        (normalize (Grounding.ground e)) := by
  change normalize (Grounding.symbols.apply _) = _
  rw [Grounding.symbols.instantiate]
  change normalize ((Grounding.ground ((Replacement.abstract ⟨x, ind⟩).apply e)).instantiate
    (Grounding.ground a)) = _
  rw [ground_abstract]
  rw [normalize_eq_of_equiv (equiv_instantiate
    ((Replacement.abstract ⟨x, ind⟩).equiv (normalize_sound (Grounding.ground e)))
    (normalize_sound (Grounding.ground a)))]
  rw [FirstOrderShape.normalize_instantiate_formula
    (Replacement.formula (Replacement.abstract_firstOrder ⟨x, ind⟩ rfl)
      (Grounding.normalize_ground_formula he)) (Grounding.normalize_ground_individual ha)]
  exact Replacement.instantiate_abstract x _ _

theorem formula_subst (x : SVar) (p t : Expr)
    (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) :
    formula (A.ofExpr (Expr.substOne x t p) (isFormula_substOne hx ht hp)) =
      Pure.substOne (Readback.variableCode x.id) (term t ht) (formula (A.ofExpr p hp)) := by
  obtain ⟨x, s⟩ := x
  cases hx
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  obtain ⟨a, ha⟩ := interpretNamed_sorted ht Names.free
  have hep := (some_formula p hp).symm
  have hat := (some_term t ht).symm
  simp only [readFormula, readTerm, normalized, he, ha, Option.map_some] at hep hat
  have hread := Readback.formula_single hep x (normalize (Grounding.ground a))
    (Grounding.normalize_ground_individual (subst_of_interpretNamed ha))
    (normalize_supported _ (Grounding.symbols.closed (subst_of_interpretNamed ha))) hat
  have hsubst := interpretNamed_substOne ⟨x, ind⟩ p t Names.free a ha
  rw [Replacement.interpretNamed_bind, he] at hsubst
  apply formula_eq_of_read
  have hn := normalize_substitute x e a (subst_of_interpretNamed he) (subst_of_interpretNamed ha)
  simp only [Term.instantiate] at hn
  simpa [readFormula, normalized, hsubst, Replacement.packed, Packed.subst, hn] using hread

end Translation
end Lisa.SCLambdaToPure
