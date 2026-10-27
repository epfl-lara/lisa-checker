import Lisa.SCLambdaToPure.OrderedToA.SubstitutionContext
/-! Rename the parameters of a simultaneous replacement rule before applying
a schematic substitution. The source and target remain α-equivalent to the
substituted original formulas. -/
namespace Lisa.SCLambdaToPure.Instantiation
open Expr Lambda

def mapContext (σ : Instantiation) (ρ : SVar → SVar) (hs : ∀ x, (ρ x).sort = x.sort)
    (ctx : SubstContext) : SubstContext where
  params := ctx.params.map ρ
  body := (σ.renameParameters ρ hs ctx.params).apply ctx.body

theorem zip_fst {xs : List SVar} {es : List Expr}
    (h : List.Forall₂ (fun x e => e.hasSort x.sort) xs es) : (xs.zip es).map Prod.fst = xs := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem zip_sorted {xs : List SVar} {es : List Expr}
    (h : List.Forall₂ (fun x e => e.hasSort x.sort) xs es) :
    ∀ p ∈ xs.zip es, p.2.hasSort p.1.sort := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hp
      · exact ih p hm

theorem mapContext_instantiate (σ : Instantiation) (ρ : SVar → SVar)
    (hρ : Function.Injective ρ) (hs : ∀ x, (ρ x).sort = x.sort)
    (ctx : SubstContext) (es : List Expr)
    (he : List.Forall₂ (fun x e => e.hasSort x.sort) ctx.params es)
    (hc : isFormula ctx.body)
    (hf : ∀ x ∈ ctx.params, ρ x ∉ σ.substitution.rangeFreeVars ∪ ctx.body.freeVars) :
    AlphaEq ((mapContext σ ρ hs ctx).instantiate (es.map σ.apply))
      (σ.apply (ctx.instantiate es)) := by
  have h := instantiate_context σ (ctx.params.zip es) (zip_sorted he) ρ hρ hs
    ctx.body hc (by simpa only [zip_fst he] using hf)
  simpa only [images, zip_fst he, apply, insertMany, mapContext,
    SubstContext.instantiate, List.zip_map] using h

def mapPair (σ : Instantiation) (p : SubstPair) : SubstPair := ⟨σ.apply p.source, σ.apply p.target⟩

theorem mapPair_sort (σ : Instantiation) (p : SubstPair) (hp : p.wellSorted) :
    (mapPair σ p).sort = p.sort := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp.1
  exact σ.hasSort hs |>.trans hs.symm

theorem mapPair_sorted (σ : Instantiation) (p : SubstPair) (hp : p.wellSorted) :
    (mapPair σ p).wellSorted := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp.1
  exact ⟨by change (σ.apply p.source).sort.isSome = true; rw [σ.hasSort hs]; rfl,
    (σ.hasSort hs).trans (σ.hasSort (hp.2.symm.trans hs)).symm⟩

def mapRule (σ : Instantiation) (ρ : SVar → SVar) (hs : ∀ x, (ρ x).sort = x.sort)
    (r : SubstRule) : SubstRule where
  comparisons := r.comparisons.map (fun p => (mapPair σ p.1, p.2.map ρ))
  context := mapContext σ ρ hs r.context

theorem rule_sorts (r : SubstRule) (hr : r.valid) :
    List.Forall₂ (fun x e => e.hasSort x.sort) r.context.params
      (r.comparisons.map (fun p => p.1.source)) ∧
    List.Forall₂ (fun x e => e.hasSort x.sort) r.context.params
      (r.comparisons.map (fun p => p.1.target)) := by
  have go (ps : List SubstPair) (xs : List SVar)
      (h : ps.map SubstPair.sort = xs.map (fun x => some x.sort))
      (hs : ∀ p ∈ ps, p.wellSorted) :
      List.Forall₂ (fun x e => e.hasSort x.sort) xs (ps.map SubstPair.source) ∧
      List.Forall₂ (fun x e => e.hasSort x.sort) xs (ps.map SubstPair.target) := by
    induction ps generalizing xs with
    | nil =>
        have hx : xs = [] := by simpa using h.symm
        subst xs; exact ⟨.nil, .nil⟩
    | cons p ps ih =>
        cases xs with
        | nil => simp at h
        | cons x xs =>
            simp only [List.map_cons, List.cons.injEq] at h
            obtain ⟨he, hf⟩ := ih xs h.2 (fun q hq => hs q (by simp [hq]))
            exact ⟨.cons h.1 he, .cons ((hs p (by simp)).2.symm.trans h.1) hf⟩
  simpa only [List.map_map, Function.comp_def] using
    go (r.comparisons.map Prod.fst) r.context.params hr.2.1 (by
      intro p hp
      obtain ⟨pair, hm, rfl⟩ := List.mem_map.mp hp
      exact (hr.2.2.1 pair hm).1)

theorem mapRule_source (σ : Instantiation) (ρ : SVar → SVar)
    (hρ : Function.Injective ρ) (hs : ∀ x, (ρ x).sort = x.sort)
    (r : SubstRule) (hr : r.valid)
    (hf : ∀ x ∈ r.context.params, ρ x ∉ σ.substitution.rangeFreeVars ∪ r.context.body.freeVars) :
    AlphaEq (mapRule σ ρ hs r).source (σ.apply r.source) := by
  simpa only [SubstRule.source, mapRule, List.map_map, Function.comp_def, mapPair] using
    mapContext_instantiate σ ρ hρ hs r.context _ (rule_sorts r hr).1 hr.1 hf

theorem mapRule_target (σ : Instantiation) (ρ : SVar → SVar)
    (hρ : Function.Injective ρ) (hs : ∀ x, (ρ x).sort = x.sort)
    (r : SubstRule) (hr : r.valid)
    (hf : ∀ x ∈ r.context.params, ρ x ∉ σ.substitution.rangeFreeVars ∪ r.context.body.freeVars) :
    AlphaEq (mapRule σ ρ hs r).target (σ.apply r.target) := by
  simpa only [SubstRule.target, mapRule, List.map_map, Function.comp_def, mapPair] using
    mapContext_instantiate σ ρ hρ hs r.context _ (rule_sorts r hr).2 hr.1 hf

theorem mapPair_params (σ : Instantiation) (ρ : SVar → SVar)
    (hρ : Function.Injective ρ) (hs : ∀ x, (ρ x).sort = x.sort)
    (p : SubstPair) (xs : List SVar) (hp : p.validParams xs)
    (hf : ∀ x ∈ xs, ρ x ∉ (σ.apply p.source).freeVars ∪ (σ.apply p.target).freeVars) :
    (mapPair σ p).validParams (xs.map ρ) := by
  refine ⟨mapPair_sorted σ p hp.1, ?_, hp.2.2.1.map hρ, ?_⟩
  · simpa only [mapPair_sort σ p hp.1, List.map_map, Function.comp_def, hs] using hp.2.1
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hf y hy

theorem mapPair_pointwise (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort)
    (p : SubstPair) (xs : List SVar) (hp : p.validParams xs) :
    AlphaBetaEta ((σ.renameParameters ρ hs xs).apply (p.pointwiseEq xs))
      ((mapPair σ p).pointwiseEq (xs.map ρ)) := by
  let τ := σ.renameParameters ρ hs xs
  obtain ⟨s, hsource⟩ := Option.isSome_iff_exists.mp hp.1.1
  have htarget := hp.1.2.symm.trans hsource
  have hargs : (xs.map Expr.var).map τ.apply = (xs.map ρ).map Expr.var := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro x hx
    change τ.lookup x = _
    simp [τ, lookup_renameParameters, hx]
  have left : AlphaBetaEta (τ.apply (p.source.applied (xs.map Expr.var)))
      ((σ.apply p.source).applied ((xs.map ρ).map Expr.var)) := by
    rw [apply_applied, hargs]
    exact alphaBetaEta_applied (.alpha (renameParameters_fresh σ ρ hs xs p.source hsource
      (fun x hx h => hp.2.2.2 x hx (Finset.mem_union_left _ h)))) _
  have right : AlphaBetaEta (τ.apply (p.target.applied (xs.map Expr.var)))
      ((σ.apply p.target).applied ((xs.map ρ).map Expr.var)) := by
    rw [apply_applied, hargs]
    exact alphaBetaEta_applied (.alpha (renameParameters_fresh σ ρ hs xs p.target htarget
      (fun x hx h => hp.2.2.2 x hx (Finset.mem_union_right _ h)))) _
  unfold SubstPair.pointwiseEq
  rw [mapPair_sort σ p hp.1]
  split <;> exact AlphaBetaEta.app (.app (.refl _) left) right

theorem mapRule_valid (σ : Instantiation) (ρ : SVar → SVar)
    (hρ : Function.Injective ρ) (hs : ∀ x, (ρ x).sort = x.sort)
    (r : SubstRule) (hr : r.valid)
    (hctx : ∀ x ∈ r.context.params, ρ x ∉ σ.substitution.rangeFreeVars ∪ r.context.body.freeVars)
    (hcmp : ∀ p ∈ r.comparisons, ∀ x ∈ p.2,
      ρ x ∉ (σ.apply p.1.source).freeVars ∪ (σ.apply p.1.target).freeVars) :
    (mapRule σ ρ hs r).valid := by
  refine ⟨(σ.renameParameters ρ hs r.context.params).hasSort hr.1, ?_, ?_, ?_, ?_⟩
  · change ((r.comparisons.map (fun p => (mapPair σ p.1, p.2.map ρ))).map Prod.fst).map SubstPair.sort = _
    simp only [List.map_map, Function.comp_def]
    have hmap : r.comparisons.map (fun p => (mapPair σ p.1).sort) =
        r.comparisons.map (fun p => p.1.sort) := by
      apply List.map_congr_left
      intro p hp
      exact mapPair_sort σ p.1 (hr.2.2.1 p hp).1
    rw [hmap]
    simpa only [SubstContext.fits, mapRule, mapContext, List.map_map, Function.comp_def, hs] using hr.2.1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact mapPair_params σ ρ hρ hs q.1 q.2 (hr.2.2.1 q hq) (hcmp q hq)
  · exact (AlphaBetaEta.alpha (mapRule_source σ ρ hρ hs r hr hctx)).preserves_sort.trans
      (σ.hasSort hr.2.2.2.1)
  · exact (AlphaBetaEta.alpha (mapRule_target σ ρ hρ hs r hr hctx)).preserves_sort.trans
      (σ.hasSort hr.2.2.2.2)

end Lisa.SCLambdaToPure.Instantiation
