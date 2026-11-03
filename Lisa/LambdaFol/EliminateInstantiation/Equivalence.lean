import Lisa.LambdaFol.ProofSystem
import Lisa.LambdaFol.EliminateInstantiation.InstantiateProof

/-! Eliminate schematic instantiation by applying substitutions throughout
the premise proofs. The converse embeds the rules without instantiation. -/
namespace Lisa.LambdaFol

/-- Embed the ordinary rules in the extended calculus. -/
noncomputable def ProofTree.ofWithoutInstantiation {Γ Δ : Finset LambdaFol.Formula} (d : WithoutInstantiation.ProofTree Γ Δ) :
    ProofTree Γ Δ := by
  induction d with
  | hypothesis p => exact .hypothesis p
  | weakening _ hΓ hΔ ih => exact .weakening ih hΓ hΔ
  | cut p _ _ ih₁ ih₂ => exact .cut p ih₁ ih₂
  | leftFalse => exact .leftFalse
  | rightTrue => exact .rightTrue
  | leftAnd p q hp hq _ ih => exact .leftAnd p q hp hq ih
  | rightAnd p q hp hq _ _ ih₁ ih₂ => exact .rightAnd p q hp hq ih₁ ih₂
  | leftOr p q hp hq _ _ ih₁ ih₂ => exact .leftOr p q hp hq ih₁ ih₂
  | rightOr p q hp hq _ ih => exact .rightOr p q hp hq ih
  | leftImp p q hp hq _ _ ih₁ ih₂ => exact .leftImp p q hp hq ih₁ ih₂
  | rightImp p q hp hq _ ih => exact .rightImp p q hp hq ih
  | leftIff p q hp hq _ ih => exact .leftIff p q hp hq ih
  | rightIff p q hp hq _ _ ih₁ ih₂ => exact .rightIff p q hp hq ih₁ ih₂
  | leftNot p hp _ ih => exact .leftNot p hp ih
  | rightNot p hp _ ih => exact .rightNot p hp ih
  | leftForall x p t hx hp ht _ ih => exact .leftForall x p t hx hp ht ih
  | rightForall x p hx hp _ hΓ hΔ ih => exact .rightForall x p hx hp ih hΓ hΔ
  | leftExists x p hx hp _ hΓ hΔ ih => exact .leftExists x p hx hp ih hΓ hΔ
  | rightExists x p t hx hp ht _ ih => exact .rightExists x p t hx hp ht ih
  | refl t ht => exact .refl t ht
  | rightEpsilon x p t hx hp ht _ ih => exact .rightEpsilon x p t hx hp ht ih
  | leftReplace r hr hf _ _ ih₁ ih₂ => exact .leftReplace r hr hf ih₁ ih₂
  | rightReplace r hr hf _ _ ih₁ ih₂ => exact .rightReplace r hr hf ih₁ ih₂

/-- Erase every instantiation step, including steps nested below other rules. -/
noncomputable def ProofTree.toWithoutInstantiation {Γ Δ : Finset LambdaFol.Formula} (d : ProofTree Γ Δ) :
    WithoutInstantiation.ProofTree Γ Δ := by
  induction d with
  | hypothesis p => exact .hypothesis p
  | weakening _ hΓ hΔ ih => exact .weakening ih hΓ hΔ
  | cut p _ _ ih₁ ih₂ => exact .cut p ih₁ ih₂
  | leftFalse => exact .leftFalse
  | rightTrue => exact .rightTrue
  | leftAnd p q hp hq _ ih => exact .leftAnd p q hp hq ih
  | rightAnd p q hp hq _ _ ih₁ ih₂ => exact .rightAnd p q hp hq ih₁ ih₂
  | leftOr p q hp hq _ _ ih₁ ih₂ => exact .leftOr p q hp hq ih₁ ih₂
  | rightOr p q hp hq _ ih => exact .rightOr p q hp hq ih
  | leftImp p q hp hq _ _ ih₁ ih₂ => exact .leftImp p q hp hq ih₁ ih₂
  | rightImp p q hp hq _ ih => exact .rightImp p q hp hq ih
  | leftIff p q hp hq _ ih => exact .leftIff p q hp hq ih
  | rightIff p q hp hq _ _ ih₁ ih₂ => exact .rightIff p q hp hq ih₁ ih₂
  | leftNot p hp _ ih => exact .leftNot p hp ih
  | rightNot p hp _ ih => exact .rightNot p hp ih
  | leftForall x p t hx hp ht _ ih => exact .leftForall x p t hx hp ht ih
  | rightForall x p hx hp _ hΓ hΔ ih => exact .rightForall x p hx hp ih hΓ hΔ
  | leftExists x p hx hp _ hΓ hΔ ih => exact .leftExists x p hx hp ih hΓ hΔ
  | rightExists x p t hx hp ht _ ih => exact .rightExists x p t hx hp ht ih
  | refl t ht => exact .refl t ht
  | rightEpsilon x p t hx hp ht _ ih => exact .rightEpsilon x p t hx hp ht ih
  | leftReplace r hr hf _ _ ih₁ ih₂ => exact .leftReplace r hr hf ih₁ ih₂
  | rightReplace r hr hf _ _ ih₁ ih₂ => exact .rightReplace r hr hf ih₁ ih₂
  | instSchema σ _ ih => exact ih.instantiate σ

/-- Instantiation adds no derivable sequents to WithoutInstantiation. Intermediate and concluding
formulas may have arbitrary higher-order free variables. -/
theorem lambdaFol_iff_withoutInstantiation {Γ Δ : Finset LambdaFol.Formula} : LambdaFol.Provable Γ Δ ↔ WithoutInstantiation.Provable Γ Δ := by
  constructor
  · rintro ⟨d⟩; exact ⟨LambdaFol.ProofTree.toWithoutInstantiation d⟩
  · rintro ⟨d⟩; exact ⟨LambdaFol.ProofTree.ofWithoutInstantiation d⟩

end Lisa.LambdaFol
