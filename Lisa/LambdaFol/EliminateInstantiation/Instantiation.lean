import Lisa.LambdaFol.ToPureFol.FormulaClasses
/-!
# Schematic instantiation on alpha-beta-eta classes

Instantiation uses the capture-avoiding operation `Subst.subst`.
This file proves that it acts on sorted expression classes and supplies the
binder-renaming laws needed to transport proofs. No normalization is involved.
-/

namespace Lisa.LambdaFol

open Expr AlphaBetaEtaNormalization

/-- A simultaneous substitution of free variables by expressions of the same sort. -/
structure Instantiation where
  substitution : Lisa.Subst
  sorted : substitution.wellSorted

namespace Instantiation

def apply (σ : Instantiation) (e : Expr) : Expr := σ.substitution.subst e

theorem hasSort (σ : Instantiation) {e : Expr} (he : e.hasSort s) :
    (σ.apply e).hasSort s := Subst.subst_preserves_hasSort σ.sorted he

def lookup (σ : Instantiation) (x : SVar) : Expr := σ.apply (.var x)

noncomputable def lambdaImages (σ : Instantiation) : Names := fun x =>
  Classical.choose (interpretNamed_sorted (σ.hasSort (e := .var x) rfl) Names.free)

theorem lambdaImages_spec (σ : Instantiation) (x : SVar) :
    interpretNamed (σ.lookup x) Names.free = some ⟨x.sort, σ.lambdaImages x⟩ :=
  Classical.choose_spec (interpretNamed_sorted (σ.hasSort (e := .var x) rfl) Names.free)

theorem interpret (σ : Instantiation) (e : Expr) :
    interpretNamed (σ.apply e) Names.free = interpretNamed e σ.lambdaImages := by
  apply interpretNamed_namedSubst
  intro x _
  have h := σ.lambdaImages_spec x
  cases he : σ.substitution.find? x with
  | none => simpa [lookup, apply, Subst.subst, he, interpretNamed] using h
  | some e => simpa [lookup, apply, Subst.subst, he] using h

/-- Only the images of free variables matter, and those images may agree up to α. -/
theorem apply_congr_alpha (σ τ : Instantiation) (e : Expr) (he : e.hasSort s)
    (h : ∀ x ∈ e.freeVars, AlphaEq (σ.lookup x) (τ.lookup x)) :
    AlphaEq (σ.apply e) (τ.apply e) := by
  apply (alpha_iff_interpretNamed_eq (σ.hasSort he) (τ.hasSort he)).mpr
  rw [σ.interpret, τ.interpret]
  apply interpretNamed_support
  intro x hx
  have hh := (alpha_iff_interpretNamed_eq (σ.hasSort (e := .var x) rfl)
    (τ.hasSort (e := .var x) rfl)).mp (h x hx)
  change interpretNamed (σ.lookup x) Names.free = interpretNamed (τ.lookup x) Names.free at hh
  rw [σ.lambdaImages_spec x, τ.lambdaImages_spec x] at hh
  simpa using hh

theorem apply_congr (σ τ : Instantiation) (e : Expr) (he : e.hasSort s)
    (h : ∀ x ∈ e.freeVars, σ.lookup x = τ.lookup x) : AlphaEq (σ.apply e) (τ.apply e) :=
  apply_congr_alpha σ τ e he (fun x hx => by rw [h x hx]; rfl)

/-- Instantiation preserves conversion, including beta and eta steps. -/
theorem preserves_alphaBetaEta (σ : Instantiation) {p q : Expr} (hp : p.hasSort s)
    (h : AlphaBetaEta p q) : AlphaBetaEta (σ.apply p) (σ.apply q) := by
  obtain ⟨e, he⟩ := interpretNamed_sorted (σ.hasSort hp) Names.free
  obtain ⟨f, hf⟩ := interpretNamed_sorted (σ.hasSort (h.preserves_sort.symm.trans hp)) Names.free
  have hh := interpretNamed_alphaBetaEta h σ.lambdaImages
  rw [← σ.interpret, ← σ.interpret, he, hf] at hh
  cases hh with
  | some hh =>
      exact (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed he Context.empty)).trans
        ((hh.reify Context.empty).trans
          (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed hf Context.empty)).symm)

noncomputable def representative (p : LambdaFol.Expression s) : Expr := Quotient.out p.val

theorem representative_sort (p : LambdaFol.Expression s) : (representative p).hasSort s := by
  have h := congrArg AlphaBetaEta.termSort (Quotient.out_eq p.val)
  exact h.trans p.property

theorem of_representative (p : LambdaFol.Expression s) :
    LambdaFol.ofExpr (representative p) (representative_sort p) = p :=
  Subtype.ext (Quotient.out_eq p.val)

noncomputable def applyClass (σ : Instantiation) (p : LambdaFol.Expression s) : LambdaFol.Expression s :=
  LambdaFol.ofExpr (σ.apply (representative p)) (σ.hasSort (representative_sort p))

@[simp] theorem applyClass_ofExpr (σ : Instantiation) (e : Expr) (he : e.hasSort s) :
    σ.applyClass (LambdaFol.ofExpr e he) = LambdaFol.ofExpr (σ.apply e) (σ.hasSort he) := by
  apply (LambdaFol.ofExpr_eq _ _).mpr
  apply σ.preserves_alphaBetaEta (representative_sort _)
  exact (LambdaFol.ofExpr_eq _ _).mp (of_representative (LambdaFol.ofExpr e he))

noncomputable def formulaSet (σ : Instantiation) (Γ : Finset LambdaFol.Formula) : Finset LambdaFol.Formula := Γ.image σ.applyClass

@[simp] theorem formulaSet_empty (σ : Instantiation) : σ.formulaSet ∅ = ∅ := Finset.image_empty _
@[simp] theorem formulaSet_singleton (σ : Instantiation) (p : LambdaFol.Formula) :
    σ.formulaSet {p} = {σ.applyClass p} := Finset.image_singleton _ _
@[simp] theorem formulaSet_insert (σ : Instantiation) (p : LambdaFol.Formula) (Γ : Finset LambdaFol.Formula) :
    σ.formulaSet (insert p Γ) = insert (σ.applyClass p) (σ.formulaSet Γ) := Finset.image_insert _ _ _
@[simp] theorem formulaSet_union (σ : Instantiation) (Γ Δ : Finset LambdaFol.Formula) :
    σ.formulaSet (Γ ∪ Δ) = σ.formulaSet Γ ∪ σ.formulaSet Δ := Finset.image_union _ _

theorem formulaSet_mono (σ : Instantiation) {Γ Δ : Finset LambdaFol.Formula} (h : Γ ⊆ Δ) :
    σ.formulaSet Γ ⊆ σ.formulaSet Δ := Finset.image_subset_image h

/-- Override the image of an eigenvariable with a fresh variable. -/
def renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort) : Instantiation :=
  ⟨σ.substitution.insert x (.var y), Subst.wellSorted_insert σ.sorted (congrArg some h)⟩

theorem lookup_renameBinder (σ : Instantiation) (x y z : SVar) (h : y.sort = x.sort) :
    (σ.renameBinder x y h).lookup z = if z = x then .var y else σ.lookup z := by
  simp only [lookup, apply, renameBinder, Subst.subst, NamedSubst.lookup_insert]
  by_cases hz : z = x <;> simp [hz]

theorem applyClass_renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (e : Expr) (he : e.hasSort s) (hx : x ∉ e.freeVars) :
    (σ.renameBinder x y h).applyClass (LambdaFol.ofExpr e he) = σ.applyClass (LambdaFol.ofExpr e he) := by
  simp only [applyClass_ofExpr]
  apply (LambdaFol.ofExpr_eq _ _).mpr
  apply AlphaBetaEta.alpha
  apply apply_congr _ _ e he
  intro z hz
  rw [lookup_renameBinder, if_neg (show z ≠ x from fun hzx => hx (hzx ▸ hz))]

theorem formulaSet_renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    {Γ : Finset LambdaFol.Formula} (hx : LambdaFol.Fresh x Γ) : (σ.renameBinder x y h).formulaSet Γ = σ.formulaSet Γ := by
  apply Finset.image_congr
  intro p hp
  obtain ⟨e, he, rfl, hf⟩ := hx p hp
  exact σ.applyClass_renameBinder x y h e he hf

/-- The fresh binder must avoid the substitution images and the original body.
Its sort is unchanged; its printed identifier is immaterial. -/
theorem interpret_renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p : Expr) (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    interpretNamed ((σ.renameBinder x y h).apply p) (Names.free.bind y) =
      interpretNamed p (σ.lambdaImages.bind x) := by
  obtain ⟨xi, s⟩ := x
  obtain ⟨yi, t⟩ := y
  cases h
  apply interpretNamed_namedSubst
  intro z hz
  simp only [renameBinder, NamedSubst.lookup_insert]
  by_cases hx : z = SVar.mk xi s
  · subst z
    simp [interpretNamed]
  · simp only [hx, ↓reduceIte]
    have hzy : z ≠ SVar.mk yi s := fun h => hy (Finset.mem_union_right _ (h ▸ hz))
    have hn := σ.lambdaImages_spec z
    cases he : σ.substitution.find? z with
    | none =>
        have hn' : Names.free z = σ.lambdaImages z := by
          simpa [lookup, apply, Subst.subst, he, interpretNamed] using hn
        simp [Names.bind_other _ hx, Names.bind_other _ hzy, hn']
    | some e =>
        dsimp only
        have hn' : interpretNamed e Names.free = some ⟨z.sort, σ.lambdaImages z⟩ := by
          simpa [lookup, apply, Subst.subst, he] using hn
        rw [interpretNamed_bind_fresh e Names.free ⟨yi, s⟩
          (fun hm => hy (Finset.mem_union_left _ (NamedSubst.lookup_freeVars he hm))), hn']
        simp [Names.bind_other _ hx, Packed.rename]

theorem lam (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p : Expr) (hp : p.hasSort s) (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    AlphaEq (σ.apply (.lam x p)) (.lam y ((σ.renameBinder x y h).apply p)) := by
  have hp' : ((σ.renameBinder x y h).apply p).sort = some s :=
    (σ.renameBinder x y h).hasSort hp
  change p.sort = some s at hp
  apply (alpha_iff_interpretNamed_eq
    (σ.hasSort (show (.lam x p : Expr).hasSort (x.sort >> s) by simp [hp]))
    (show (.lam y ((σ.renameBinder x y h).apply p) : Expr).hasSort (x.sort >> s) by
      simp [Expr.hasSort, hp', h])).mpr
  rw [σ.interpret]
  simp only [interpretNamed, σ.interpret_renameBinder x y h p hy, h]

/-- Substitution into a quantified body commutes with schematic instantiation
after choosing a fresh name for the bound variable. -/
theorem substOne (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p t : Expr) (hp : p.hasSort s) (ht : t.hasSort x.sort)
    (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    AlphaBetaEta (σ.apply (Expr.substOne x t p))
      (Expr.substOne y (σ.apply t) ((σ.renameBinder x y h).apply p)) := by
  change p.sort = some s at hp
  change t.sort = some x.sort at ht
  have hb := σ.preserves_alphaBetaEta
    (show (.app (.lam x p) t : Expr).hasSort s by simp [hp, ht])
    (AlphaBetaEta.beta x p t ht)
  exact hb.symm.trans ((AlphaBetaEta.app (.alpha (σ.lam x y h p hp hy)) (.refl _)).trans
    (AlphaBetaEta.beta y _ _ (h ▸ σ.hasSort ht)))

@[simp] theorem apply_bot (σ : Instantiation) : σ.apply bot = bot := rfl
@[simp] theorem apply_top (σ : Instantiation) : σ.apply top = top := rfl
@[simp] theorem apply_and (σ : Instantiation) (p q : Expr) :
    σ.apply (and p q) = and (σ.apply p) (σ.apply q) := rfl
@[simp] theorem apply_or (σ : Instantiation) (p q : Expr) :
    σ.apply (or p q) = or (σ.apply p) (σ.apply q) := rfl
@[simp] theorem apply_imp (σ : Instantiation) (p q : Expr) :
    σ.apply (imp p q) = imp (σ.apply p) (σ.apply q) := rfl
@[simp] theorem apply_iff (σ : Instantiation) (p q : Expr) :
    σ.apply (iff p q) = iff (σ.apply p) (σ.apply q) := rfl
@[simp] theorem apply_neg (σ : Instantiation) (p : Expr) :
    σ.apply (neg p) = neg (σ.apply p) := rfl
@[simp] theorem apply_eq (σ : Instantiation) (t u : Expr) :
    σ.apply (eq t u) = eq (σ.apply t) (σ.apply u) := rfl

theorem applyClass_forall (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p : Expr) (hx : x.sort = ind) (hp : isFormula p)
    (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.applyClass (LambdaFol.ofExpr (forall_ x p) (isFormula_forall hx hp)) =
      LambdaFol.ofExpr (forall_ y ((σ.renameBinder x y h).apply p))
        (isFormula_forall (h.trans hx) ((σ.renameBinder x y h).hasSort hp)) := by
  rw [applyClass_ofExpr]
  apply (LambdaFol.ofExpr_eq _ _).mpr
  exact .app (.refl _) (.alpha (σ.lam x y h p hp hy))

theorem applyClass_exists (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p : Expr) (hx : x.sort = ind) (hp : isFormula p)
    (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.applyClass (LambdaFol.ofExpr (exists_ x p) (isFormula_exists hx hp)) =
      LambdaFol.ofExpr (exists_ y ((σ.renameBinder x y h).apply p))
        (isFormula_exists (h.trans hx) ((σ.renameBinder x y h).hasSort hp)) := by
  rw [applyClass_ofExpr]
  apply (LambdaFol.ofExpr_eq _ _).mpr
  exact .app (.refl _) (.alpha (σ.lam x y h p hp hy))

theorem applyClass_substOne (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p t : Expr) (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t)
    (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.applyClass (LambdaFol.ofExpr (Expr.substOne x t p) (isFormula_substOne hx ht hp)) =
      LambdaFol.ofExpr (Expr.substOne y (σ.apply t) ((σ.renameBinder x y h).apply p))
        (isFormula_substOne (h.trans hx) (σ.hasSort ht) ((σ.renameBinder x y h).hasSort hp)) := by
  rw [applyClass_ofExpr]
  apply (LambdaFol.ofExpr_eq _ _).mpr
  exact σ.substOne x y h p t hp (hx ▸ ht) hy

theorem applyClass_epsilon_subst (σ : Instantiation) (x y : SVar) (hy : y.sort = x.sort)
    (p : Expr) (hx : x.sort = ind) (hp : isFormula p)
    (hf : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.applyClass (LambdaFol.ofExpr (Expr.substOne x (Expr.epsilon_ (.lam x p)) p)
      (isFormula_substOne hx (isTerm_epsilon hx hp) hp)) =
    LambdaFol.ofExpr (Expr.substOne y (Expr.epsilon_ (.lam y ((σ.renameBinder x y hy).apply p)))
      ((σ.renameBinder x y hy).apply p))
      (isFormula_substOne (hy.trans hx)
        (isTerm_epsilon (hy.trans hx) ((σ.renameBinder x y hy).hasSort hp))
        ((σ.renameBinder x y hy).hasSort hp)) := by
  rw [applyClass_ofExpr]
  apply (LambdaFol.ofExpr_eq _ _).mpr
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

/-- A finite set of names sufficient for choosing fresh representatives of a formula set. -/
noncomputable def representativeFreeVars (Γ : Finset LambdaFol.Formula) : Finset SVar :=
  Γ.biUnion (fun p => (representative p).freeVars)

theorem fresh_of_not_mem_support {Γ : Finset LambdaFol.Formula} {x : SVar} (hx : x ∉ representativeFreeVars Γ) :
    LambdaFol.Fresh x Γ := by
  intro p hp
  exact ⟨representative p, representative_sort p, of_representative p,
    fun h => hx (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)⟩

def fresh (s : LSort) (xs : Finset SVar) : {y : SVar // y.sort = s ∧ y ∉ xs} := by
  let y : SVar := ⟨freshId (xs.image SVar.id) ⟨"_inst", 0⟩, s⟩
  exact ⟨y, rfl, fun h => freshId_not_mem (xs.image SVar.id) ⟨"_inst", 0⟩
    (Finset.mem_image.mpr ⟨y, h, rfl⟩)⟩

/-- Choose an eigenvariable fresh for the body, substitution images, and both
substituted formula sets. These are exactly the side conditions of the eigenrules. -/
noncomputable def freshEigenvariable (σ : Instantiation) (s : LSort) (p : Expr)
    (Γ Δ : Finset LambdaFol.Formula) :
    {y : SVar // y.sort = s ∧ y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars ∧
      LambdaFol.Fresh y (σ.formulaSet Γ) ∧ LambdaFol.Fresh y (σ.formulaSet Δ)} := by
  obtain ⟨y, hy, hf⟩ := fresh s
    ((σ.substitution.rangeFreeVars ∪ p.freeVars) ∪ representativeFreeVars (σ.formulaSet Γ) ∪ representativeFreeVars (σ.formulaSet Δ))
  simp only [Finset.mem_union, not_or] at hf
  exact ⟨y, hy, by simpa only [Finset.mem_union, not_or] using hf.1.1,
    fresh_of_not_mem_support hf.1.2, fresh_of_not_mem_support hf.2⟩

end Instantiation
end Lisa.LambdaFol

namespace Lisa.LambdaFol

theorem formulaSet_image (σ : Instantiation) (Γ : Finset Expr) (hΓ : isFSet Γ)
    (hσΓ : isFSet (Γ.image σ.apply)) :
    formulaSet (Γ.image σ.apply) hσΓ = σ.formulaSet (formulaSet Γ hΓ) := by
  ext p
  simp only [mem_formulaSet, Instantiation.formulaSet, Finset.mem_image]
  constructor
  · rintro ⟨e, ⟨q, hq, rfl⟩, he⟩
    exact ⟨ofExpr q (hΓ q hq), ⟨q, hq, rfl⟩, by simpa using he⟩
  · rintro ⟨q, ⟨e, he, rfl⟩, hq⟩
    exact ⟨σ.apply e, ⟨e, he, rfl⟩, by simpa using hq⟩

end Lisa.LambdaFol
