import Lisa.SCLambdaToPure.A

/-! Properties of A's formula classes, freshness, and sequent conversion. -/
namespace Lisa.SCLambdaToPure.A
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

/-- Normalization changes representatives, not the formulas of system A. -/
theorem ofExpr_normalize {p q : Expr} (hp : isFormula p)
    (h : Lambda.normalizeNamed p = some q) :
    ofExpr p hp = ofExpr q ((Lambda.normalizeNamed_sort h).symm.trans hp) :=
  (ofExpr_eq _ _).mpr (Lambda.normalizeNamed_sound h)

theorem mem_context {Γ : Finset Expr} (hΓ : isFSet Γ) (p : Formula) :
    p ∈ context Γ hΓ ↔ ∃ e, ∃ he : e ∈ Γ, ofExpr e (hΓ e he) = p := by
  simp only [context, Finset.mem_image, Finset.mem_attach, true_and]
  exact ⟨fun ⟨e, h⟩ => ⟨e.val, e.property, h⟩,
    fun ⟨e, he, h⟩ => ⟨⟨e, he⟩, h⟩⟩

@[simp] theorem context_empty (h : isFSet ∅) : context ∅ h = ∅ := by
  ext p; simp [mem_context]

@[simp] theorem context_insert (p : Expr) (Γ : Finset Expr) (hp : isFormula p)
    (hΓ : isFSet Γ) :
    context (insert p Γ) (isFSet_insert hp hΓ) = insert (ofExpr p hp) (context Γ hΓ) := by
  ext q
  simp only [mem_context, Finset.mem_insert]
  constructor
  · rintro ⟨e, he, h⟩
    rcases he with rfl | he
    · exact Or.inl h.symm
    · exact Or.inr ⟨e, he, h⟩
  · rintro (rfl | ⟨e, he, h⟩)
    · exact ⟨p, Or.inl rfl, rfl⟩
    · exact ⟨e, Or.inr he, h⟩

@[simp] theorem context_insert_any (p : Expr) (Γ : Finset Expr) (h : isFSet (insert p Γ)) :
    context (insert p Γ) h = insert (ofExpr p (h p (by simp)))
      (context Γ (fun e he => h e (Finset.mem_insert_of_mem he))) :=
  context_insert p Γ _ _

@[simp] theorem context_singleton (p : Expr) (hp : isFormula p) :
    context {p} (isFSet_insert (Γ := ∅) hp (by simp [isFSet])) = {ofExpr p hp} := by
  simpa using context_insert p ∅ hp (by simp [isFSet])

@[simp] theorem context_union (Γ Δ : Finset Expr) (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    context (Γ ∪ Δ) (isFSet_union hΓ hΔ) = context Γ hΓ ∪ context Δ hΔ := by
  ext p
  simp only [mem_context, Finset.mem_union]
  constructor
  · rintro ⟨e, he, h⟩
    exact he.elim (fun he => Or.inl ⟨e, he, h⟩) (fun he => Or.inr ⟨e, he, h⟩)
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, Or.inl he, h⟩
    · exact ⟨e, Or.inr he, h⟩

@[simp] theorem context_union_any (Γ Δ : Finset Expr) (h : isFSet (Γ ∪ Δ)) :
    context (Γ ∪ Δ) h = context Γ (fun e he => h e (Finset.mem_union_left _ he)) ∪
      context Δ (fun e he => h e (Finset.mem_union_right _ he)) := context_union Γ Δ _ _

theorem context_mono {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (h : Γ ⊆ Δ) : context Γ hΓ ⊆ context Δ hΔ := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := (mem_context hΓ p).mp hp
  exact (mem_context hΔ _).mpr ⟨e, h he, rfl⟩

end Lisa.SCLambdaToPure.A

/-! Individual equality substitution, derived from A's generalized replacement rule. -/
namespace Lisa.SCLambdaToPure.A
open Expr

namespace ProofTree

private def individualRule (x : SVar) (p t u : Expr) : SubstRule :=
  ⟨[(⟨t, u⟩, [])], ⟨[x], p⟩⟩

private theorem individualRule_valid (hx : x.sort = ind) (hp : isFormula p)
    (ht : isTerm t) (hu : isTerm u) : (individualRule x p t u).valid := by
  refine ⟨hp, ?_, ?_, isFormula_substOne hx ht hp, isFormula_substOne hx hu hp⟩
  · simp [individualRule, SubstContext.fits, SubstPair.sort, show t.sort = some ind from ht, hx]
  · simp [individualRule, SubstPair.validParams, SubstPair.wellSorted,
      SubstPair.sort, Expr.wellSorted, show t.sort = some ind from ht, show u.sort = some ind from hu, LSort.splitArgs]

private theorem individualRule_fresh : RuleFresh (individualRule x p t u) Θ Ξ := by
  simp [RuleFresh, individualRule]

/-- Individual substitution is the empty-parameter case of generalized replacement. -/
def leftSubst {Γ Δ Θ Ξ} (x : SVar) (p t u : Expr)
    (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) (hu : isTerm u)
    (d : ProofTree (insert (ofExpr (substOne x t p) (isFormula_substOne hx ht hp)) Γ) Δ)
    (e : ProofTree Θ (insert (ofExpr (eq t u) (isFormula_eq ht hu)) Ξ)) :
    ProofTree (insert (ofExpr (substOne x u p) (isFormula_substOne hx hu hp))
      (Γ ∪ Θ)) (Δ ∪ Ξ) := by
  apply leftReplace (individualRule x p t u) (individualRule_valid hx hp ht hu)
    individualRule_fresh d
  simpa [individualRule, SubstRule.equation, SubstPair.pointwiseEq,
    SubstPair.sort, show t.sort = some ind from ht, LSort.splitArgs, foldFormulas, Expr.applied] using e

/-- The right-hand version is derived from the same generalized rule. -/
def rightSubst {Γ Δ Θ Ξ} (x : SVar) (p t u : Expr)
    (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) (hu : isTerm u)
    (d : ProofTree Γ (insert (ofExpr (substOne x t p) (isFormula_substOne hx ht hp)) Δ))
    (e : ProofTree Θ (insert (ofExpr (eq t u) (isFormula_eq ht hu)) Ξ)) :
    ProofTree (Γ ∪ Θ) (insert (ofExpr (substOne x u p) (isFormula_substOne hx hu hp))
      (Δ ∪ Ξ)) := by
  apply rightReplace (individualRule x p t u) (individualRule_valid hx hp ht hu)
    individualRule_fresh d
  simpa [individualRule, SubstRule.equation, SubstPair.pointwiseEq,
    SubstPair.sort, show t.sort = some ind from ht, LSort.splitArgs, foldFormulas, Expr.applied] using e

end ProofTree

end Lisa.SCLambdaToPure.A
