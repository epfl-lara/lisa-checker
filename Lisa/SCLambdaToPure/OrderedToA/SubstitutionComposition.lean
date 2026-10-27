import Lisa.SCLambdaToPure.OrderedToA.Substitution
import Lisa.SCLambdaToPure.AToPure.Replacement
/-! Composition and finite overrides for the substitution-elimination proof.
These are operations on syntax; they do not translate a derivation to Pure.
-/
namespace Lisa.SCLambdaToPure.Instantiation
open Lambda

private def composeSubst (σ : Instantiation) : Lisa.Subst → Lisa.Subst
  | .nil => σ.substitution
  | .cons x e rest => .cons x (σ.apply e) (composeSubst σ rest)

private theorem composeSubst_sorted (σ : Instantiation) (τ : Lisa.Subst)
    (hτ : τ.wellSorted) : (composeSubst σ τ).wellSorted := by
  induction τ with
  | nil => exact σ.sorted
  | cons x e rest ih => exact ⟨σ.hasSort hτ.1, ih hτ.2⟩

/-- Apply `τ` first and `σ` second, preserving simultaneous substitution. -/
def comp (σ τ : Instantiation) : Instantiation :=
  ⟨composeSubst σ τ.substitution, composeSubst_sorted σ τ.substitution τ.sorted⟩

private theorem composeSubst_lookup (σ : Instantiation) (τ : Lisa.Subst) (x : SVar) :
    (composeSubst σ τ).find? x =
      match τ.find? x with
      | some e => some (σ.apply e)
      | none => σ.substitution.find? x := by
  induction τ with
  | nil => rfl
  | cons y e rest ih =>
      by_cases h : y = x
      · subst y; simp [composeSubst, Lean.AssocList.find?]
      · simp [composeSubst, Lean.AssocList.find?, Bool.beq_eq_decide_eq, h, ih]

theorem lookup_comp (σ τ : Instantiation) (x : SVar) :
    (σ.comp τ).lookup x = σ.apply (τ.lookup x) := by
  simp only [lookup, apply, comp, Subst.subst, composeSubst_lookup]
  cases τ.substitution.find? x <;> rfl

/-- A named substitution as a replacement on intrinsically sorted terms. -/
noncomputable def replacement (σ : Instantiation) : Replacement where
  bound := Sub.id
  free s x := σ.names ⟨x, s⟩
  const _ c := .const c

theorem replacement_interpret (σ : Instantiation) (e : Expr) :
    (interpretNamed e Names.free).map σ.replacement.packed =
      interpretNamed (σ.apply e) Names.free := by
  rw [Replacement.interpretNamed_apply _ (by intros; rfl), σ.interpret]
  rfl

theorem names_comp (σ τ : Instantiation) (x : SVar) :
    (σ.comp τ).names x = σ.replacement.apply (τ.names x) := by
  have h := σ.replacement_interpret (τ.lookup x)
  rw [τ.names_spec x, ← lookup_comp, (σ.comp τ).names_spec x] at h
  simpa only [Option.map_some, Replacement.packed, Option.some.injEq,
    Sigma.mk.inj_iff, heq_eq_eq, true_and] using h.symm

theorem apply_comp (σ τ : Instantiation) (e : Expr) (he : e.hasSort s) :
    AlphaEq ((σ.comp τ).apply e) (σ.apply (τ.apply e)) := by
  apply (alpha_iff_interpretNamed_eq ((σ.comp τ).hasSort he)
    (σ.hasSort (τ.hasSort he))).mpr
  rw [(σ.comp τ).interpret, ← σ.replacement_interpret, τ.interpret,
    Replacement.interpretNamed_apply _ (by intros; rfl)]
  congr 1
  funext x
  exact names_comp σ τ x

end Lisa.SCLambdaToPure.Instantiation
