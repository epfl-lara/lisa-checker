import Lisa.Lambda.Normalization

/-! AlphaBetaEta preservation gives the canonical substitution/renaming equations. -/
namespace Lisa.Lambda

theorem normalize_subst (e : Term s) (σ : Sub) :
    normalize ((normalize e).subst σ) = normalize (e.subst σ) :=
  (normalize_eq_of_equiv ((normalize_sound e).subst σ)).symm

theorem normalize_rename (e : Term s) (ρ : Ren) :
    normalize ((normalize e).rename ρ) = normalize (e.rename ρ) :=
  (normalize_eq_of_equiv ((normalize_sound e).rename ρ)).symm
end Lisa.Lambda
