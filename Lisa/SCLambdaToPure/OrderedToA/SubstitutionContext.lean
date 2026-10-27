import Lisa.SCLambdaToPure.OrderedToA.SubstitutionBinding
import Lisa.Ordered

/-! Simultaneous contexts commute with schematic substitution after freshening
their formal parameters. Replacement images are never substituted into each other. -/
namespace Lisa.SCLambdaToPure.Instantiation
open Lambda

def identity : Instantiation := ⟨.nil, trivial⟩

theorem apply_identity (e : Expr) (he : e.hasSort s) : AlphaEq (identity.apply e) e := by
  apply (alpha_iff_interpretNamed_eq (identity.hasSort he) he).mpr
  rw [identity.interpret]
  apply interpretNamed_support
  intro x _
  have h := identity.names_spec x
  simpa only [lookup, apply, identity, Subst.subst, Lean.AssocList.find?, interpretNamed,
    Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and, Names.free] using h.symm

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
  rw [σ.names_spec x, τ.names_spec x] at hh
  simpa using hh

def insertMany (σ : Lisa.Subst) (ps : List (SVar × Expr)) : Lisa.Subst :=
  ps.foldl (fun σ (x, e) => σ.insert x e) σ

def lastImage (ps : List (SVar × Expr)) (x : SVar) : Option Expr :=
  (ps.reverse.find? (fun p => p.1 == x)).map Prod.snd

@[simp] theorem lastImage_nil (x : SVar) : lastImage [] x = none := rfl

theorem lastImage_cons (p : SVar × Expr) (ps : List (SVar × Expr)) (x : SVar) :
    lastImage (p :: ps) x = (lastImage ps x).orElse
      (fun _ => if x = p.1 then some p.2 else none) := by
  simp only [lastImage, List.reverse_cons, List.find?_append]
  cases h : ps.reverse.find? (fun p => p.1 == x) with
  | some p => rfl
  | none =>
      simp only [Option.orElse_none, Option.map_none]
      by_cases hx : x = p.1
      · subst x; simp
      · simp [List.find?, Bool.beq_eq_decide_eq, show p.1 ≠ x from Ne.symm hx, hx]

theorem lookup_insertMany (σ : Lisa.Subst) (ps : List (SVar × Expr)) (x : SVar) :
    (insertMany σ ps).find? x = (lastImage ps x).orElse (fun _ => σ.find? x) := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih =>
      rw [insertMany, List.foldl_cons]
      change (insertMany (σ.insert p.1 p.2) ps).find? x = _
      rw [ih, lastImage_cons, NamedSubst.lookup_insert]
      cases lastImage ps x <;> by_cases hx : x = p.1 <;> simp [hx]

theorem lastImage_none (ps : List (SVar × Expr)) (x : SVar) :
    lastImage ps x = none ↔ x ∉ ps.map Prod.fst := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [lastImage_cons]
      cases h : lastImage ps x with
      | none =>
          have hx := ih.mp h
          by_cases he : x = p.1 <;> simp [he, hx]
      | some e =>
          have hx : x ∈ ps.map Prod.fst := by
            by_contra hn
            have := ih.mpr hn
            simp [h] at this
          simp [hx]

theorem lastImage_map (ps : List (SVar × Expr)) (ρ : SVar → SVar)
    (hρ : Function.Injective ρ) (f : Expr → Expr) (x : SVar) :
    lastImage (ps.map (fun p => (ρ p.1, f p.2))) (ρ x) = (lastImage ps x).map f := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, lastImage_cons, ih]
      cases lastImage ps x <;> by_cases hx : x = p.1 <;> simp [hx, hρ.eq_iff]

theorem insertMany_sorted (σ : Lisa.Subst) (hσ : σ.wellSorted)
    (ps : List (SVar × Expr)) (h : ∀ p ∈ ps, p.2.hasSort p.1.sort) :
    (insertMany σ ps).wellSorted := by
  induction ps generalizing σ with
  | nil => exact hσ
  | cons p ps ih =>
      exact ih _ (Subst.wellSorted_insert hσ (h p (by simp)))
        (fun q hq => h q (by simp [hq]))

def images (ps : List (SVar × Expr)) (h : ∀ p ∈ ps, p.2.hasSort p.1.sort) : Instantiation :=
  ⟨insertMany .nil ps, insertMany_sorted .nil trivial ps h⟩

theorem lookup_images (ps : List (SVar × Expr)) (h : ∀ p ∈ ps, p.2.hasSort p.1.sort) (x : SVar) :
    (images ps h).lookup x = (lastImage ps x).getD (.var x) := by
  simp only [lookup, apply, images, Subst.subst, lookup_insertMany, Lean.AssocList.find?]
  cases lastImage ps x <;> rfl

theorem images_fresh (ps : List (SVar × Expr)) (h : ∀ p ∈ ps, p.2.hasSort p.1.sort)
    (e : Expr) (he : e.hasSort s) (hf : ∀ x ∈ ps.map Prod.fst, x ∉ e.freeVars) :
    AlphaEq ((images ps h).apply e) e := by
  apply Eq.trans (apply_congr (images ps h) identity e he ?_) (apply_identity e he)
  intro x hx
  rw [lookup_images, (lastImage_none ps x).mpr (fun hm => hf x hm hx)]
  rfl

theorem lookup_support (σ : Instantiation) (x : SVar) :
    (σ.lookup x).freeVars ⊆ σ.substitution.rangeFreeVars ∪ {x} := by
  intro y hy
  cases h : σ.substitution.find? x with
  | none =>
      simp only [lookup, apply, Subst.subst, h, Expr.freeVars] at hy
      exact Finset.mem_union_right _ hy
  | some e =>
      simp only [lookup, apply, Subst.subst, h] at hy
      exact Finset.mem_union_left _ (NamedSubst.lookup_freeVars h hy)

theorem mapped_images_sorted (σ : Instantiation) (ps : List (SVar × Expr))
    (h : ∀ p ∈ ps, p.2.hasSort p.1.sort) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) :
    ∀ p ∈ ps.map (fun p => (ρ p.1, σ.apply p.2)), p.2.hasSort p.1.sort := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simpa only [hs] using σ.hasSort (h q hq)

/-- Freshen a context's parameters before applying `σ` to its body. Filling the
result with the substituted images is the same simultaneous operation, up to α. -/
theorem instantiate_context (σ : Instantiation) (ps : List (SVar × Expr))
    (h : ∀ p ∈ ps, p.2.hasSort p.1.sort) (ρ : SVar → SVar)
    (hρ : Function.Injective ρ) (hs : ∀ x, (ρ x).sort = x.sort)
    (e : Expr) (he : e.hasSort s)
    (hf : ∀ x ∈ ps.map Prod.fst, ρ x ∉ σ.substitution.rangeFreeVars ∪ e.freeVars) :
    AlphaEq
      ((images (ps.map (fun p => (ρ p.1, σ.apply p.2)))
        (mapped_images_sorted σ ps h ρ hs)).apply
          ((σ.renameParameters ρ hs (ps.map Prod.fst)).apply e))
      (σ.apply ((images ps h).apply e)) := by
  let old := images ps h
  let new := images (ps.map (fun p => (ρ p.1, σ.apply p.2)))
    (mapped_images_sorted σ ps h ρ hs)
  let body := σ.renameParameters ρ hs (ps.map Prod.fst)
  apply Eq.trans (apply_comp new body e he).symm
  apply Eq.trans (apply_congr_alpha (new.comp body) (σ.comp old) e he ?_)
    (apply_comp σ old e he)
  intro x hx
  rw [lookup_comp, lookup_comp]
  simp only [body, lookup_renameParameters]
  by_cases hm : x ∈ ps.map Prod.fst
  · rw [if_pos hm]
    change AlphaEq (new.lookup (ρ x)) (σ.apply (old.lookup x))
    simp only [new, old, lookup_images, lastImage_map ps ρ hρ]
    cases hlast : lastImage ps x with
    | none => exact False.elim (((lastImage_none ps x).mp hlast) hm)
    | some a => rfl
  · rw [if_neg hm]
    have ho : old.lookup x = .var x := by
      simp only [old, lookup_images, (lastImage_none ps x).mpr hm, Option.getD_none]
    rw [ho]
    change AlphaEq (new.apply (σ.lookup x)) (σ.lookup x)
    apply images_fresh _ _ _ (σ.hasSort (e := .var x) rfl)
    intro y hy hmem
    simp only [List.map_map, Function.comp_def] at hy
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hy
    have hfree := lookup_support σ x hmem
    apply hf pair.1 (List.mem_map.mpr ⟨pair, hp, rfl⟩)
    rcases Finset.mem_union.mp hfree with hr | hr
    · exact Finset.mem_union_left _ hr
    · have hEq := Finset.mem_singleton.mp hr
      exact Finset.mem_union_right _ (hEq.symm ▸ hx)

end Lisa.SCLambdaToPure.Instantiation
