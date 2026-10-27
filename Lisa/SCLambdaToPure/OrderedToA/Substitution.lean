import Lisa.SCLambdaToPure.AToPure.FormulaClasses
/-!
# Schematic instantiation on alpha-beta-eta classes

The executable substitution is the existing capture-avoiding `Subst.subst`.
This file proves that it acts on sorted expression classes and supplies the
binder-renaming laws needed to transport proofs. No normalization is involved.
-/

namespace Lisa.SCLambdaToPure

open Expr Lambda

/-- A simultaneous substitution of free variables by expressions of the same sort. -/
structure Instantiation where
  substitution : Lisa.Subst
  sorted : substitution.wellSorted

namespace Instantiation

def apply (σ : Instantiation) (e : Expr) : Expr := σ.substitution.subst e

theorem hasSort (σ : Instantiation) {e : Expr} (he : e.hasSort s) :
    (σ.apply e).hasSort s := Subst.subst_preserves_hasSort σ.sorted he

def lookup (σ : Instantiation) (x : SVar) : Expr := σ.apply (.var x)

noncomputable def names (σ : Instantiation) : Names := fun x =>
  Classical.choose (interpretNamed_sorted (σ.hasSort (e := .var x) rfl) Names.free)

theorem names_spec (σ : Instantiation) (x : SVar) :
    interpretNamed (σ.lookup x) Names.free = some ⟨x.sort, σ.names x⟩ :=
  Classical.choose_spec (interpretNamed_sorted (σ.hasSort (e := .var x) rfl) Names.free)

theorem interpret (σ : Instantiation) (e : Expr) :
    interpretNamed (σ.apply e) Names.free = interpretNamed e σ.names := by
  apply interpretNamed_namedSubst
  intro x _
  have h := σ.names_spec x
  cases he : σ.substitution.find? x with
  | none => simpa [lookup, apply, Subst.subst, he, interpretNamed] using h
  | some e => simpa [lookup, apply, Subst.subst, he] using h

/-- Instantiation preserves conversion, including beta and eta steps. -/
theorem equivalent (σ : Instantiation) {p q : Expr} (hp : p.hasSort s)
    (h : AlphaBetaEta p q) : AlphaBetaEta (σ.apply p) (σ.apply q) := by
  obtain ⟨e, he⟩ := interpretNamed_sorted (σ.hasSort hp) Names.free
  obtain ⟨f, hf⟩ := interpretNamed_sorted (σ.hasSort (h.preserves_sort.symm.trans hp)) Names.free
  have hh := interpretNamed_alphaBetaEta h σ.names
  rw [← σ.interpret, ← σ.interpret, he, hf] at hh
  cases hh with
  | some hh =>
      exact (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed he Context.empty)).trans
        ((hh.reify Context.empty).trans
          (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed hf Context.empty)).symm)

noncomputable def representative (p : A.Expression s) : Expr := Quotient.out p.val

theorem representative_sort (p : A.Expression s) : (representative p).hasSort s := by
  have h := congrArg AlphaBetaEta.termSort (Quotient.out_eq p.val)
  exact h.trans p.property

theorem of_representative (p : A.Expression s) :
    A.ofExpr (representative p) (representative_sort p) = p :=
  Subtype.ext (Quotient.out_eq p.val)

noncomputable def expression (σ : Instantiation) (p : A.Expression s) : A.Expression s :=
  A.ofExpr (σ.apply (representative p)) (σ.hasSort (representative_sort p))

@[simp] theorem expression_ofExpr (σ : Instantiation) (e : Expr) (he : e.hasSort s) :
    σ.expression (A.ofExpr e he) = A.ofExpr (σ.apply e) (σ.hasSort he) := by
  apply (A.ofExpr_eq _ _).mpr
  apply σ.equivalent (representative_sort _)
  exact (A.ofExpr_eq _ _).mp (of_representative (A.ofExpr e he))

noncomputable def context (σ : Instantiation) (Γ : A.Context) : A.Context := Γ.image σ.expression

@[simp] theorem context_empty (σ : Instantiation) : σ.context ∅ = ∅ := Finset.image_empty _
@[simp] theorem context_singleton (σ : Instantiation) (p : A.Formula) :
    σ.context {p} = {σ.expression p} := Finset.image_singleton _ _
@[simp] theorem context_insert (σ : Instantiation) (p : A.Formula) (Γ : A.Context) :
    σ.context (insert p Γ) = insert (σ.expression p) (σ.context Γ) := Finset.image_insert _ _ _
@[simp] theorem context_union (σ : Instantiation) (Γ Δ : A.Context) :
    σ.context (Γ ∪ Δ) = σ.context Γ ∪ σ.context Δ := Finset.image_union _ _

theorem context_mono (σ : Instantiation) {Γ Δ : A.Context} (h : Γ ⊆ Δ) :
    σ.context Γ ⊆ σ.context Δ := Finset.image_subset_image h

/-- Override the image of an eigenvariable with a fresh variable. -/
def renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort) : Instantiation :=
  ⟨σ.substitution.insert x (.var y), Subst.wellSorted_insert σ.sorted (congrArg some h)⟩

theorem lookup_renameBinder (σ : Instantiation) (x y z : SVar) (h : y.sort = x.sort) :
    (σ.renameBinder x y h).lookup z = if z = x then .var y else σ.lookup z := by
  simp only [lookup, apply, renameBinder, Subst.subst, NamedSubst.lookup_insert]
  by_cases hz : z = x <;> simp [hz]

theorem names_renameBinder_other (σ : Instantiation) (x y z : SVar)
    (h : y.sort = x.sort) (hz : z ≠ x) :
    (σ.renameBinder x y h).names z = σ.names z := by
  have h₁ := (σ.renameBinder x y h).names_spec z
  rw [lookup_renameBinder, if_neg hz, σ.names_spec] at h₁
  simpa using h₁.symm

theorem expression_renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (e : Expr) (he : e.hasSort s) (hx : x ∉ e.freeVars) :
    (σ.renameBinder x y h).expression (A.ofExpr e he) = σ.expression (A.ofExpr e he) := by
  simp only [expression_ofExpr]
  apply (A.ofExpr_eq _ _).mpr
  apply AlphaBetaEta.alpha
  apply (alpha_iff_interpretNamed_eq ((σ.renameBinder x y h).hasSort he) (σ.hasSort he)).mpr
  rw [interpret, interpret]
  exact interpretNamed_support e _ _ (fun z hz => σ.names_renameBinder_other x y z h
    (fun hzx => hx (hzx ▸ hz)))

theorem context_renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    {Γ : A.Context} (hx : A.Fresh x Γ) : (σ.renameBinder x y h).context Γ = σ.context Γ := by
  apply Finset.image_congr
  intro p hp
  obtain ⟨e, he, rfl, hf⟩ := hx p hp
  exact σ.expression_renameBinder x y h e he hf

/-- The fresh binder must avoid the substitution images and the original body.
Its sort is unchanged; its printed identifier is immaterial. -/
theorem interpret_renameBinder (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p : Expr) (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    interpretNamed ((σ.renameBinder x y h).apply p) (Names.free.bind y) =
      interpretNamed p (σ.names.bind x) := by
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
    have hn := σ.names_spec z
    cases he : σ.substitution.find? z with
    | none =>
        have hn' : Names.free z = σ.names z := by
          simpa [lookup, apply, Subst.subst, he, interpretNamed] using hn
        simp [Names.bind_other _ hx, Names.bind_other _ hzy, hn']
    | some e =>
        dsimp only
        have hn' : interpretNamed e Names.free = some ⟨z.sort, σ.names z⟩ := by
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
  have hb := σ.equivalent
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

theorem expression_forall (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p : Expr) (hx : x.sort = ind) (hp : isFormula p)
    (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.expression (A.ofExpr (forall_ x p) (isFormula_forall hx hp)) =
      A.ofExpr (forall_ y ((σ.renameBinder x y h).apply p))
        (isFormula_forall (h.trans hx) ((σ.renameBinder x y h).hasSort hp)) := by
  rw [expression_ofExpr]
  apply (A.ofExpr_eq _ _).mpr
  exact .app (.refl _) (.alpha (σ.lam x y h p hp hy))

theorem expression_exists (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p : Expr) (hx : x.sort = ind) (hp : isFormula p)
    (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.expression (A.ofExpr (exists_ x p) (isFormula_exists hx hp)) =
      A.ofExpr (exists_ y ((σ.renameBinder x y h).apply p))
        (isFormula_exists (h.trans hx) ((σ.renameBinder x y h).hasSort hp)) := by
  rw [expression_ofExpr]
  apply (A.ofExpr_eq _ _).mpr
  exact .app (.refl _) (.alpha (σ.lam x y h p hp hy))

theorem expression_substOne (σ : Instantiation) (x y : SVar) (h : y.sort = x.sort)
    (p t : Expr) (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t)
    (hy : y ∉ σ.substitution.rangeFreeVars ∪ p.freeVars) :
    σ.expression (A.ofExpr (Expr.substOne x t p) (isFormula_substOne hx ht hp)) =
      A.ofExpr (Expr.substOne y (σ.apply t) ((σ.renameBinder x y h).apply p))
        (isFormula_substOne (h.trans hx) (σ.hasSort ht) ((σ.renameBinder x y h).hasSort hp)) := by
  rw [expression_ofExpr]
  apply (A.ofExpr_eq _ _).mpr
  exact σ.substOne x y h p t hp (hx ▸ ht) hy

/-- A finite set of names sufficient for choosing fresh representatives of a context. -/
noncomputable def support (Γ : A.Context) : Finset SVar :=
  Γ.biUnion (fun p => (representative p).freeVars)

theorem fresh_of_not_mem_support {Γ : A.Context} {x : SVar} (hx : x ∉ support Γ) :
    A.Fresh x Γ := by
  intro p hp
  exact ⟨representative p, representative_sort p, of_representative p,
    fun h => hx (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)⟩

def fresh (s : LSort) (xs : Finset SVar) : {y : SVar // y.sort = s ∧ y ∉ xs} := by
  let y : SVar := ⟨freshId (xs.image SVar.id) ⟨"_inst", 0⟩, s⟩
  exact ⟨y, rfl, fun h => freshId_not_mem (xs.image SVar.id) ⟨"_inst", 0⟩
    (Finset.mem_image.mpr ⟨y, h, rfl⟩)⟩

end Instantiation
end Lisa.SCLambdaToPure

namespace Lisa.SCLambdaToPure.A

theorem context_image (σ : Instantiation) (Γ : Finset Expr) (hΓ : isFSet Γ)
    (hσΓ : isFSet (Γ.image σ.apply)) :
    context (Γ.image σ.apply) hσΓ = σ.context (context Γ hΓ) := by
  ext p
  simp only [mem_context, Instantiation.context, Finset.mem_image]
  constructor
  · rintro ⟨e, ⟨q, hq, rfl⟩, he⟩
    exact ⟨ofExpr q (hΓ q hq), ⟨q, hq, rfl⟩, by simpa using he⟩
  · rintro ⟨q, ⟨e, he, rfl⟩, hq⟩
    exact ⟨σ.apply e, ⟨e, he, rfl⟩, by simpa using hq⟩

end Lisa.SCLambdaToPure.A
