import Lisa.LambdaFol.EliminateInstantiation.InstantiateRuleData
import Lisa.LambdaFol.ToPureFol.TranslateNamedExpressions
import Lisa.LambdaFol.ToPureFol.RelatedExpressions
import Lisa.Ordered

/-! Transport simultaneous source substitutions through arbitrary formula
templates. For a repeated parameter, the last replacement wins. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization

def ProvablyRelatedExpr (Γ Δ : Finset (PureFol.Formula PureFolTranslation.language)) (R : FirstOrderAssignment)
    (e f : Expr) : Prop :=
  ∃ (s : LSort) (he : e.hasSort s) (hf : f.hasSort s), ProvablyRelated Γ Δ s (R.applyExpr e he) (R.applyExpr f hf)

theorem provablyRelatedExpr_iff {e f : Expr} (he : e.hasSort s) (hf : f.hasSort s) :
    ProvablyRelatedExpr Γ Δ R e f ↔ ProvablyRelated Γ Δ s (R.applyExpr e he) (R.applyExpr f hf) := by
  constructor
  · rintro ⟨t, ht, hu, h⟩
    have hs : s = t := Option.some.inj (he.symm.trans ht)
    subst t
    exact h
  · intro h; exact ⟨s, he, hf, h⟩

theorem applyExpr_substitution_congr (R : FirstOrderAssignment) (σ τ : Instantiation)
    (e : Expr) (he : e.hasSort s)
    (h : ∀ x, ProvablyRelatedExpr Γ Δ R (σ.lookup x) (τ.lookup x)) :
    ProvablyRelated Γ Δ s (R.applyExpr (σ.apply e) (σ.hasSort he))
      (R.applyExpr (τ.apply e) (τ.hasSort he)) := by
  rw [R.applyExpr_instantiate σ e he, R.applyExpr_instantiate τ e he]
  obtain ⟨t, ht⟩ := interpretNamed_sorted he Names.free
  rw [(R.instantiate σ).applyExpr_of_named e he ht, (R.instantiate τ).applyExpr_of_named e he ht]
  apply apply_preserves_related
  constructor
  · intro u n; exact related_refl _
  · intro u x
    have hh := (provablyRelatedExpr_iff (σ.hasSort (e := .var ⟨x, u⟩) rfl)
      (τ.hasSort (e := .var ⟨x, u⟩) rfl)).mp (h ⟨x, u⟩)
    rw [R.applyExpr_of_named (σ.apply (.var ⟨x, u⟩)) (σ.hasSort (e := .var ⟨x, u⟩) rfl) (σ.lambdaImages_spec ⟨x, u⟩),
      R.applyExpr_of_named (τ.apply (.var ⟨x, u⟩)) (τ.hasSort (e := .var ⟨x, u⟩) rfl) (τ.lambdaImages_spec ⟨x, u⟩)] at hh
    exact hh
  · intro u c; exact related_refl _

private theorem replacements_related (R : FirstOrderAssignment) (xs : List SVar) (es fs : List Expr)
    (h : List.Forall₂ (ProvablyRelatedExpr Γ Δ R) es fs) (σ τ : Lisa.Subst)
    (hστ : ∀ x, ProvablyRelatedExpr Γ Δ R (σ.subst (.var x)) (τ.subst (.var x))) :
    ∀ x, ProvablyRelatedExpr Γ Δ R ((Instantiation.insertMany σ (xs.zip es)).subst (.var x))
      ((Instantiation.insertMany τ (xs.zip fs)).subst (.var x)) := by
  induction xs generalizing es fs σ τ with
  | nil => exact hστ
  | cons x xs ih =>
      cases h with
      | nil => exact hστ
      | @cons e f es fs hef hrest =>
          apply ih es fs hrest (σ.insert x e) (τ.insert x f)
          intro y
          simp only [Subst.subst, NamedSubst.lookup_insert]
          by_cases hy : y = x
          · simpa [hy] using hef
          · simpa [hy, Subst.subst] using hστ y

/-- The actual source template operation transports simultaneous pointwise
comparisons, including replacements at higher sorts. -/
theorem template_congr (R : FirstOrderAssignment) (ctx : SubstContext) (es fs : List Expr)
    (he : List.Forall₂ (fun x e => e.hasSort x.sort) ctx.params es)
    (hf : List.Forall₂ (fun x e => e.hasSort x.sort) ctx.params fs)
    (hc : isFormula ctx.body) (h : List.Forall₂ (ProvablyRelatedExpr Γ Δ R) es fs) :
    ProvablyRelatedExpr Γ Δ R (ctx.instantiate es) (ctx.instantiate fs) := by
  let σ := Instantiation.ofPairs (ctx.params.zip es) (Instantiation.zip_sorted he)
  let τ := Instantiation.ofPairs (ctx.params.zip fs) (Instantiation.zip_sorted hf)
  refine ⟨prop, σ.hasSort hc, τ.hasSort hc, ?_⟩
  apply applyExpr_substitution_congr R σ τ ctx.body hc
  apply replacements_related R ctx.params es fs h .nil .nil
  intro x
  exact ⟨x.sort, rfl, rfl, related_refl _⟩

end Lisa.LambdaFol

/-! Translate generalized simultaneous replacement into PureFol derivations. Fresh
pointwise parameters may be assigned arbitrary scoped expressions, establishing
relatedness of the compared functions before replacement in a formula template. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization

private theorem app_sort {f a : Expr} (hf : f.hasSort (s >> t)) (ha : a.hasSort s) :
    (Expr.app f a).hasSort t := by
  dsimp only [Expr.hasSort] at hf ha ⊢
  simp [Expr.sort, hf, ha]

/-- A comparison derivable for every assignment to its fresh parameters gives
the relation at the full function sort, with the same residual formula sets. -/
theorem applyExpr_extensional (s : LSort) (xs : List SVar)
    (hx : xs.map SVar.sort = s.splitArgs.1) (hn : xs.Nodup)
    (p q : Expr) (hp : p.hasSort s) (hq : q.hasSort s)
    (hf : ∀ x ∈ xs, x ∉ p.freeVars ∪ q.freeVars) (R : FirstOrderAssignment)
    (h : ∀ S, S.const = R.const → AgreeOutside xs S R →
      ProvablyRelated Γ Δ s.splitArgs.2
        (S.applyExpr (p.applied (xs.map Expr.var)) (SubstPair.applied_splitArgs_sort s hp xs hx))
        (S.applyExpr (q.applied (xs.map Expr.var)) (SubstPair.applied_splitArgs_sort s hq xs hx))) :
    ProvablyRelated Γ Δ s (R.applyExpr p hp) (R.applyExpr q hq) := by
  induction s generalizing xs p q R with
  | ind | prop =>
      have he : xs = [] := by simpa [LSort.splitArgs] using hx
      subst xs
      exact h R rfl (fun _ _ => rfl)
  | arrow a b _ ih =>
      cases xs with
      | nil => simp [LSort.splitArgs] at hx
      | cons x xs =>
          rcases x with ⟨id, sort⟩
          simp only [List.map_cons, LSort.splitArgs, List.cons.injEq] at hx
          rcases hx with ⟨hsa, hxtail⟩
          change sort = a at hsa
          subst sort
          let x : SVar := ⟨id, a⟩
          have hnx : x ∉ xs := (List.nodup_cons.mp hn).1
          have htail := (List.nodup_cons.mp hn).2
          have hp' := app_sort hp (show (Expr.var x).hasSort a from rfl)
          have hq' := app_sort hq (show (Expr.var x).hasSort a from rfl)
          intro u v huv
          let S := R.update x u
          have hpS : S.applyExpr p hp = R.applyExpr p hp :=
            R.applyExpr_update_fresh x u p hp (fun hm => (hf x (by simp [x])) (by simp [hm]))
          have hqS : S.applyExpr q hq = R.applyExpr q hq :=
            R.applyExpr_update_fresh x u q hq (fun hm => (hf x (by simp [x])) (by simp [hm]))
          have hd := ih xs hxtail htail (.app p (.var x)) (.app q (.var x)) hp' hq' (by
            intro y hy
            have hyx : y ≠ x := fun he => hnx (he ▸ hy)
            have fresh := hf y (by simp [hy])
            simpa [hyx] using fresh) S (by
              intro U hc hu
              apply h U hc
              intro y hy
              have parts : y ≠ x ∧ y ∉ xs := by simpa only [List.mem_cons, not_or] using hy
              exact (hu y parts.2).trans (R.update_other x u parts.1))
          rw [FirstOrderAssignment.applyExpr_app S (a := .var x) hp rfl,
            FirstOrderAssignment.applyExpr_app S (a := .var x) hq rfl,
            FirstOrderAssignment.applyExpr_var, hpS, hqS] at hd
          have hd' : ProvablyRelated Γ Δ b ((R.applyExpr p hp).app u) ((R.applyExpr q hq).app u) := by
            simpa only [S, FirstOrderAssignment.update_self] using hd
          exact hd'.trans (related_refl (R.applyExpr q hq) u v huv)

/-! Syntactic transport of the generalized simultaneous substitution rule.
The comparison premise is translated uniformly in its fresh parameters. Its
residual formula sets are retained; the main premise need not be fresh for them. -/

private theorem fold_and_member (R : FirstOrderAssignment) (hR : R.FixesConstants) (es : List Expr)
    (hs : ∀ e ∈ es, isFormula e) (p : Expr) (hp : p ∈ es) :
    PureFol.Provable {R.toPureFolFormula (foldFormulas Expr.and Expr.top es)} {R.toPureFolFormula p} := by
  -- Combine the separate assumptions using left-conjunction, starting from
  -- the hypothesis for the selected member. No cuts are needed.
  have go (xs : List Expr) (a : Expr) (ha : isFormula a)
      (hs : ∀ e ∈ xs, isFormula e)
      (d : PureFol.ProofTree (insert (R.toPureFolFormula a) (xs.map R.toPureFolFormula).toFinset) {R.toPureFolFormula p}) :
      PureFol.ProofTree {R.toPureFolFormula (xs.foldl Expr.and a)} {R.toPureFolFormula p} := by
    induction xs generalizing a with
    | nil => simpa using d
    | cons b bs ih =>
        have hb := hs b (by simp)
        apply ih (Expr.and a b) (isFormula_and ha hb) (fun e he => hs e (by simp [he]))
        simpa [R.toPureFolFormula_and hR ha hb] using
          PureFol.ProofTree.leftAnd (R.toPureFolFormula a) (R.toPureFolFormula b) (by simpa using d)
  cases es with
  | nil => simp at hp
  | cons a es =>
      exact ⟨go es a (hs a (by simp)) (fun e he => hs e (by simp [he]))
        (.hypothesisIn (R.toPureFolFormula p) (by simpa using List.mem_map.mpr ⟨p, hp, rfl⟩) (by simp))⟩

private theorem ground_related (R : FirstOrderAssignment) (hR : R.FixesConstants) (s : LSort)
    (hs : s = ind ∨ s = prop) (p q : Expr) (hp : p.hasSort s) (hq : q.hasSort s)
    (h : PureFol.Provable Γ (insert (R.toPureFolFormula (if s = prop then Expr.iff p q else Expr.eq p q)) Δ)) :
    ProvablyRelated Γ Δ s (R.applyExpr p hp) (R.applyExpr q hq) := by
  rcases hs with rfl | rfl
  · simp only [if_neg (show ind ≠ prop by decide), R.toPureFolFormula_eq hR hp hq] at h
    exact h
  · simp only [↓reduceIte, R.toPureFolFormula_iff hR hp hq,
      R.toPureFolFormula_of_sorted p hp, R.toPureFolFormula_of_sorted q hq] at h
    exact h

theorem pointwise_related (R : FirstOrderAssignment) (r : SubstPair) (xs : List SVar)
    (hr : r.validParams xs) (s : LSort) (hs : r.source.hasSort s)
    (h : ∀ S, S.const = R.const → AgreeOutside xs S R →
      PureFol.Provable Γ (insert (S.toPureFolFormula (r.pointwiseEq xs)) Δ))
    (hR : R.FixesConstants) :
    ProvablyRelated Γ Δ s (R.applyExpr r.source hs) (R.applyExpr r.target (hr.1.2.symm.trans hs)) := by
  have hx : xs.map SVar.sort = s.splitArgs.1 := by
    simpa [SubstPair.sort, show r.source.sort = some s from hs] using hr.2.1
  apply applyExpr_extensional s xs hx hr.2.2.1 r.source r.target hs _ hr.2.2.2 R
  intro S hc hS
  have hlogical : S.FixesConstants := by intro u c hh; rw [hc]; exact hR u c hh
  have hh := h S hc hS
  have hp := SubstPair.applied_splitArgs_sort s hs xs hx
  have hq := SubstPair.applied_splitArgs_sort s (hr.1.2.symm.trans hs) xs hx
  apply ground_related S hlogical s.splitArgs.2 (SubstPair.splitArgs_ground s) _ _ hp hq
  simpa only [SubstPair.pointwiseEq, SubstPair.sort, show r.source.sort = some s from hs,
    Option.map_some, Option.some.injEq] using hh

/-- Translate the comparison premise of the actual source rule into a target
proof that its simultaneously instantiated source and target formulas are
equivalent. No assumptions on the main premise's formula sets occur here. -/
theorem replacement_preserves_provable_iff (R : FirstOrderAssignment) (hR : R.FixesConstants)
    (r : SubstRule) (hr : r.valid)
    (Θ Ξ : FirstOrderAssignment → Finset (PureFol.Formula PureFolTranslation.language))
    (fresh : ∀ pair ∈ r.comparisons, ∀ S : FirstOrderAssignment, S.const = R.const →
      AgreeOutside pair.2 S R → Θ S = Θ R ∧ Ξ S = Ξ R)
    (proof : ∀ S : FirstOrderAssignment, S.FixesConstants →
      PureFol.Provable (Θ S) (insert (S.toPureFolFormula r.equation) (Ξ S))) :
    PureFol.Provable (Θ R)
      (insert (.iff (R.toPureFolFormula r.source) (R.toPureFolFormula r.target)) (Ξ R)) := by
  have each (pair : SubstPair × List SVar) (hm : pair ∈ r.comparisons) :
      ProvablyRelatedExpr (Θ R) (Ξ R) R pair.1.source pair.1.target := by
    have hv := hr.2.2.1 pair hm
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hv.1.1
    refine ⟨s, hs, hv.1.2.symm.trans hs, ?_⟩
    apply pointwise_related R pair.1 pair.2 hv s hs _ hR
    intro S hc hS
    have hlogical : S.FixesConstants := by intro u c hh; rw [hc]; exact hR u c hh
    obtain ⟨d⟩ := proof S hlogical
    obtain ⟨proj⟩ := fold_and_member S hlogical
      (r.comparisons.map (fun pair => pair.1.pointwiseEq pair.2)) (by
        intro p hp
        obtain ⟨pair, hm, rfl⟩ := List.mem_map.mp hp
        exact SubstPair.pointwiseEq_isFormula (hr.2.2.1 pair hm))
      (pair.1.pointwiseEq pair.2) (List.mem_map.mpr ⟨pair, hm, rfl⟩)
    rw [(fresh pair hm S hc hS).1, (fresh pair hm S hc hS).2] at d
    refine ⟨?_⟩
    simpa using PureFol.ProofTree.cut (Δ := Ξ R) (Θ := ∅)
      (Ξ := {S.toPureFolFormula (pair.1.pointwiseEq pair.2)}) (S.toPureFolFormula r.equation) d proj
  have sorts := Instantiation.rule_sorts r hr
  have hs := template_congr R r.context
    (r.comparisons.map (fun pair => pair.1.source))
    (r.comparisons.map (fun pair => pair.1.target))
    sorts.1
    sorts.2 hr.1
    (by simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same] using each)
  have hh := (provablyRelatedExpr_iff hr.2.2.2.1 hr.2.2.2.2).mp hs
  simpa only [FirstOrderAssignment.toPureFolFormula_of_sorted R r.source hr.2.2.2.1,
    FirstOrderAssignment.toPureFolFormula_of_sorted R r.target hr.2.2.2.2] using hh

end Lisa.LambdaFol
