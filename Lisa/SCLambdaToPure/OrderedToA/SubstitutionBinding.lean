import Lisa.SCLambdaToPure.OrderedToA.SubstitutionComposition
import Lisa.SCLambdaToPure.AToPure.Syntax
/-! Fresh parameter lists for pushing substitution through an inference rule. -/
namespace Lisa.SCLambdaToPure.Instantiation
open Lambda

theorem names_eq_of_lookup_eq (σ τ : Instantiation) (x : SVar)
    (h : σ.lookup x = τ.lookup x) : σ.names x = τ.names x := by
  have hh := σ.names_spec x
  rw [h, τ.names_spec x] at hh
  simpa using hh.symm

theorem apply_congr (σ τ : Instantiation) (e : Expr) (he : e.hasSort s)
    (h : ∀ x ∈ e.freeVars, σ.lookup x = τ.lookup x) : AlphaEq (σ.apply e) (τ.apply e) := by
  apply (alpha_iff_interpretNamed_eq (σ.hasSort he) (τ.hasSort he)).mpr
  rw [σ.interpret, τ.interpret]
  exact interpretNamed_support e _ _ (fun x hx => names_eq_of_lookup_eq σ τ x (h x hx))

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

theorem context_renameParameters (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) (xs : List SVar) (Γ : A.Context)
    (hf : ∀ x ∈ xs, A.Fresh x Γ) :
    (σ.renameParameters ρ hs xs).context Γ = σ.context Γ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [renameParameters, context_renameBinder _ _ _ _ (hf x (by simp))]
      exact ih (fun y hy => hf y (by simp [hy]))

/-- A sort-preserving injection whose image avoids a given finite set. -/
def freshParameters (avoid : Finset SVar) (x : SVar) : SVar :=
  ⟨⟨x.id.name, avoid.sup (fun y => y.id.idx) + 1 + x.id.idx⟩, x.sort⟩

theorem freshParameters_sort (avoid : Finset SVar) (x : SVar) :
    (freshParameters avoid x).sort = x.sort := rfl

theorem freshParameters_injective (avoid : Finset SVar) :
    Function.Injective (freshParameters avoid) := by
  intro x y h
  have hs := congrArg SVar.sort h
  have hi := congrArg (fun z : SVar => z.id.idx) h
  have hn := congrArg (fun z : SVar => z.id.name) h
  have hid : x.id = y.id := by
    cases x with | mk xi xs =>
      cases y with | mk yi ys =>
        cases xi; cases yi
        exact congrArg₂ Identifier.mk hn (Nat.add_left_cancel hi)
  cases x; cases y; cases hid; cases hs; rfl

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

theorem expression_epsilon_subst (σ : Instantiation) (x y : SVar) (hy : y.sort = x.sort)
    (p : Expr) (hx : x.sort = ind) (hp : isFormula p)
    (hf : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.expression (A.ofExpr (Expr.substOne x (Expr.epsilon_ (.lam x p)) p)
      (isFormula_substOne hx (isTerm_epsilon hx hp) hp)) =
    A.ofExpr (Expr.substOne y (Expr.epsilon_ (.lam y ((σ.renameBinder x y hy).apply p)))
      ((σ.renameBinder x y hy).apply p))
      (isFormula_substOne (hy.trans hx)
        (isTerm_epsilon (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp))
        ((σ.renameBinder x y hy).hasSort hp)) := by
  rw [expression_ofExpr]
  apply (A.ofExpr_eq _ _).mpr
  have ht := isTerm_epsilon hx hp
  have ht' := σ.hasSort ht
  have he : AlphaBetaEta (σ.apply (Expr.epsilon_ (.lam x p)))
      (Expr.epsilon_ (.lam y ((σ.renameBinder x y hy).apply p))) :=
    .app (.refl _) (.alpha (σ.lam x y hy p hp hf))
  exact (σ.substOne x y hy p _ hp (hx ▸ ht) hf).trans
    ((AlphaBetaEta.beta y _ _ ((hy.trans hx) ▸ ht')).symm.trans
      ((AlphaBetaEta.app (.refl _) he).trans
        (AlphaBetaEta.beta y _ _ ((hy.trans hx) ▸
          isTerm_epsilon (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp)))))

end Lisa.SCLambdaToPure.Instantiation
