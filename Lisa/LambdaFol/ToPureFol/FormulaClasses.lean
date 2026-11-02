import Lisa.LambdaFol.Syntax

/-! Properties of the shared formula classes, freshness, and sequent conversion. -/
namespace Lisa.LambdaFol
open Expr

@[simp] theorem ofExpr_eq {e f : Expr} (he : e.hasSort s) (hf : f.hasSort s) :
    ofExpr e he = ofExpr f hf ↔ AlphaBetaEta e f := by
  simp [ofExpr, Subtype.ext_iff]

theorem fresh_of_representatives (x : SVar) (Γ : Finset Expr) (hΓ : isFSet Γ)
    (hx : ∀ e ∈ Γ, x ∉ e.freeVars) :
    Fresh x (Γ.attach.image (fun e : {e // e ∈ Γ} => ofExpr e.val (hΓ e.val e.property))) := by
  intro p hp
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨e.val, hΓ e.val e.property, rfl, hx e.val e.property⟩

theorem mem_formulaSet {Γ : Finset Expr} (hΓ : isFSet Γ) (p : Formula) :
    p ∈ formulaSet Γ hΓ ↔ ∃ e, ∃ he : e ∈ Γ, ofExpr e (hΓ e he) = p := by
  simp only [formulaSet, Finset.mem_image, Finset.mem_attach, true_and]
  exact ⟨fun ⟨e, h⟩ => ⟨e.val, e.property, h⟩,
    fun ⟨e, he, h⟩ => ⟨⟨e, he⟩, h⟩⟩

@[simp] theorem formulaSet_empty (h : isFSet ∅) : formulaSet ∅ h = ∅ := by
  ext p; simp [mem_formulaSet]

@[simp] theorem formulaSet_insert (p : Expr) (Γ : Finset Expr) (hp : isFormula p)
    (hΓ : isFSet Γ) :
    formulaSet (insert p Γ) (isFSet_insert hp hΓ) = insert (ofExpr p hp) (formulaSet Γ hΓ) := by
  ext q
  simp only [mem_formulaSet, Finset.mem_insert]
  aesop

@[simp] theorem formulaSet_insert_any (p : Expr) (Γ : Finset Expr) (h : isFSet (insert p Γ)) :
    formulaSet (insert p Γ) h = insert (ofExpr p (h p (by simp)))
      (formulaSet Γ (fun e he => h e (Finset.mem_insert_of_mem he))) :=
  formulaSet_insert p Γ _ _

@[simp] theorem formulaSet_union (Γ Δ : Finset Expr) (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    formulaSet (Γ ∪ Δ) (isFSet_union hΓ hΔ) = formulaSet Γ hΓ ∪ formulaSet Δ hΔ := by
  ext p
  simp only [mem_formulaSet, Finset.mem_union]
  aesop

@[simp] theorem formulaSet_union_any (Γ Δ : Finset Expr) (h : isFSet (Γ ∪ Δ)) :
    formulaSet (Γ ∪ Δ) h = formulaSet Γ (fun e he => h e (Finset.mem_union_left _ he)) ∪
      formulaSet Δ (fun e he => h e (Finset.mem_union_right _ he)) := formulaSet_union Γ Δ _ _

theorem formulaSet_mono {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (h : Γ ⊆ Δ) : formulaSet Γ hΓ ⊆ formulaSet Δ hΔ := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := (mem_formulaSet hΓ p).mp hp
  exact (mem_formulaSet hΔ _).mpr ⟨e, h he, rfl⟩

end Lisa.LambdaFol
