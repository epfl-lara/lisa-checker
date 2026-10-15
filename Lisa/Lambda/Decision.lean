import Lisa.Lambda.Normalization

namespace Lisa.Lambda

deriving instance DecidableEq for Var
deriving instance DecidableEq for Term

/-- Decide alpha-beta-eta equivalence by comparing total, eta-long readbacks. -/
instance : DecidableRel (@Equiv Γ s) := fun e f =>
  decidable_of_iff (normalize e = normalize f) (equiv_iff_normalize_eq e f).symm

end Lisa.Lambda
