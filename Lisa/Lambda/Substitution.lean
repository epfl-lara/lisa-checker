import Lisa.Lambda.Normalization

namespace Lisa.Lambda

/-- Normalize before or after substitution without changing the canonical result. -/
theorem normalize_subst (e : Term Γ s) (σ : Sub Γ Δ) :
    normalize ((normalize e).subst σ) = normalize (e.subst σ) :=
  (normalize_eq_of_equiv ((normalize_sound e).subst σ)).symm

/-- Normalize before or after renaming without changing the canonical result. -/
theorem normalize_rename (e : Term Γ s) (ρ : Ren Γ Δ) :
    normalize ((normalize e).rename ρ) = normalize (e.rename ρ) :=
  (normalize_eq_of_equiv ((normalize_sound e).rename ρ)).symm

end Lisa.Lambda
