import Lisa.LambdaFol.EliminateInstantiation.InstantiationComposition
import Lisa.LambdaFol.ToPureFol.SignatureAndVariables
/-! Fresh parameter lists for pushing substitution through an inference rule. -/
namespace Lisa.LambdaFol.Instantiation
open AlphaBetaEtaNormalization

/-- Replace a finite list of names using a sort-preserving renaming.
Repeated parameters receive the same image. -/
def renameParameters (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) : List SVar → Instantiation
  | [] => σ
  | x :: xs => (renameParameters σ ρ hs xs).renameBinder x (ρ x) (hs x)

theorem lookup_renameParameters (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) (xs : List SVar) (x : SVar) :
    (σ.renameParameters ρ hs xs).lookup x =
      if x ∈ xs then .var (ρ x) else σ.lookup x := by
  induction xs with
  | nil => rfl
  | cons y xs ih =>
      simp only [renameParameters, lookup_renameBinder, ih, List.mem_cons]
      by_cases h : x = y <;> simp [h]

theorem renameParameters_fresh (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) (xs : List SVar)
    (e : Expr) (he : e.hasSort s) (hf : ∀ x ∈ xs, x ∉ e.freeVars) :
    AlphaEq ((σ.renameParameters ρ hs xs).apply e) (σ.apply e) := by
  apply apply_congr _ _ e he
  intro x hx
  rw [lookup_renameParameters, if_neg (fun hm => hf x hm hx)]

theorem formulaSet_renameParameters (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) (xs : List SVar) (Γ : Finset LambdaFol.Formula)
    (hf : ∀ x ∈ xs, LambdaFol.Fresh x Γ) :
    (σ.renameParameters ρ hs xs).formulaSet Γ = σ.formulaSet Γ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [renameParameters, formulaSet_renameBinder _ _ _ _ (hf x (by simp))]
      exact ih (fun y hy => hf y (by simp [hy]))

/-- A sort-preserving injection whose image avoids a given finite set. -/
def freshParameters (avoid : Finset SVar) (x : SVar) : SVar :=
  ⟨⟨x.id.name, avoid.sup (fun y => y.id.idx) + 1 + x.id.idx⟩, x.sort⟩

theorem freshParameters_sort (avoid : Finset SVar) (x : SVar) :
    (freshParameters avoid x).sort = x.sort := rfl

theorem freshParameters_injective (avoid : Finset SVar) :
    Function.Injective (freshParameters avoid) := by
  rintro ⟨⟨xn, xi⟩, xs⟩ ⟨⟨yn, yi⟩, ys⟩ h
  simpa [freshParameters] using h

theorem freshParameters_fresh (avoid : Finset SVar) (x : SVar) :
    freshParameters avoid x ∉ avoid := by
  intro h
  have hh := Finset.le_sup (f := fun y : SVar => y.id.idx) h
  change avoid.sup (fun y => y.id.idx) + 1 + x.id.idx ≤ _ at hh
  omega

theorem apply_applied (σ : Instantiation) (f : Expr) (es : List Expr) :
    σ.apply (f.applied es) = (σ.apply f).applied (es.map σ.apply) := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih => exact ih (.app f e)

theorem alphaBetaEta_applied {f g : Expr} (h : AlphaBetaEta f g) (es : List Expr) :
    AlphaBetaEta (f.applied es) (g.applied es) := by
  induction es generalizing f g with
  | nil => exact h
  | cons e es ih => exact ih (.app h (.refl e))


end Lisa.LambdaFol.Instantiation
