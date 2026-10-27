import Lisa.SCLambdaToPure.OrderedToA.SubstitutionRule
import Lisa.SCLambdaToPure.AToPure.Translation
import Lisa.Ordered

/-! Transport simultaneous source substitutions through arbitrary formula
contexts. Repeated parameters retain the existing last-replacement convention. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda

def RelatedExpr (Γ Δ : Pure.Context Readback.language) (R : Assignment)
    (e f : Expr) : Prop :=
  ∃ (s : LSort) (he : e.hasSort s) (hf : f.hasSort s), Related Γ Δ s (R.expression e he) (R.expression f hf)

theorem relatedExpr_iff {e f : Expr} (he : e.hasSort s) (hf : f.hasSort s) :
    RelatedExpr Γ Δ R e f ↔ Related Γ Δ s (R.expression e he) (R.expression f hf) := by
  constructor
  · rintro ⟨t, ht, hu, h⟩
    have hs : s = t := Option.some.inj (he.symm.trans ht)
    subst t
    exact h
  · intro h; exact ⟨s, he, hf, h⟩

theorem expression_substitution_congr (R : Assignment) (σ τ : Instantiation)
    (e : Expr) (he : e.hasSort s)
    (h : ∀ x, RelatedExpr Γ Δ R (σ.lookup x) (τ.lookup x)) :
    Related Γ Δ s (R.expression (σ.apply e) (σ.hasSort he))
      (R.expression (τ.apply e) (τ.hasSort he)) := by
  rw [R.expression_instantiate σ e he, R.expression_instantiate τ e he]
  obtain ⟨t, ht⟩ := interpretNamed_sorted he Names.free
  rw [(R.instantiate σ).expression_of_named e he ht, (R.instantiate τ).expression_of_named e he ht]
  apply fundamental
  constructor
  · intro u n; exact related_refl _
  · intro u x
    have hh := (relatedExpr_iff (σ.hasSort (e := .var ⟨x, u⟩) rfl)
      (τ.hasSort (e := .var ⟨x, u⟩) rfl)).mp (h ⟨x, u⟩)
    rw [R.expression_of_named (σ.apply (.var ⟨x, u⟩)) (σ.hasSort (e := .var ⟨x, u⟩) rfl) (σ.names_spec ⟨x, u⟩),
      R.expression_of_named (τ.apply (.var ⟨x, u⟩)) (τ.hasSort (e := .var ⟨x, u⟩) rfl) (τ.names_spec ⟨x, u⟩)] at hh
    exact hh
  · intro u c; exact related_refl _

private def replacements (xs : List SVar) (es : List Expr) (σ : Lisa.Subst) : Lisa.Subst :=
  Instantiation.insertMany σ (xs.zip es)

private theorem replacements_sorted (xs : List SVar) (es : List Expr)
    (h : List.Forall₂ (fun x e => e.hasSort x.sort) xs es)
    (σ : Lisa.Subst) (hσ : σ.wellSorted) : (replacements xs es σ).wellSorted :=
  Instantiation.insertMany_sorted σ hσ _ (Instantiation.zip_sorted h)

private theorem replacements_related (R : Assignment) (xs : List SVar) (es fs : List Expr)
    (h : List.Forall₂ (RelatedExpr Γ Δ R) es fs) (σ τ : Lisa.Subst)
    (hστ : ∀ x, RelatedExpr Γ Δ R (σ.subst (.var x)) (τ.subst (.var x))) :
    ∀ x, RelatedExpr Γ Δ R ((replacements xs es σ).subst (.var x))
      ((replacements xs fs τ).subst (.var x)) := by
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

/-- The actual source context operation transports simultaneous pointwise
comparisons, including replacements at higher sorts. -/
theorem context_congr (R : Assignment) (ctx : SubstContext) (es fs : List Expr)
    (he : List.Forall₂ (fun x e => e.hasSort x.sort) ctx.params es)
    (hf : List.Forall₂ (fun x e => e.hasSort x.sort) ctx.params fs)
    (hc : isFormula ctx.body) (h : List.Forall₂ (RelatedExpr Γ Δ R) es fs) :
    RelatedExpr Γ Δ R (ctx.instantiate es) (ctx.instantiate fs) := by
  let σ : Instantiation := ⟨replacements ctx.params es .nil,
    replacements_sorted ctx.params es he .nil trivial⟩
  let τ : Instantiation := ⟨replacements ctx.params fs .nil,
    replacements_sorted ctx.params fs hf .nil trivial⟩
  refine ⟨prop, σ.hasSort hc, τ.hasSort hc, ?_⟩
  apply expression_substitution_congr R σ τ ctx.body hc
  apply replacements_related R ctx.params es fs h .nil .nil
  intro x
  exact ⟨x.sort, rfl, rfl, related_refl _⟩

end Lisa.SCLambdaToPure.Syntactic

/-! Translate generalized simultaneous replacement into Pure derivations. Fresh
pointwise parameters may be assigned arbitrary scoped expressions, establishing
relatedness of the compared functions before replacement in a formula context. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda

def AgreeOutside (xs : List SVar) (R S : Assignment) : Prop :=
  ∀ x, x ∉ xs → R.free x.sort x.id = S.free x.sort x.id

private theorem app_sort {f a : Expr} (hf : f.hasSort (s >> t)) (ha : a.hasSort s) :
    (Expr.app f a).hasSort t := by
  dsimp only [Expr.hasSort] at hf ha ⊢
  simp [Expr.sort, hf, ha]

/-- A comparison derivable for every assignment to its fresh parameters gives
the relation at the full function sort, with the same residual contexts. -/
theorem expression_extensional (s : LSort) (xs : List SVar)
    (hx : xs.map SVar.sort = s.splitArgs.1) (hn : xs.Nodup)
    (p q : Expr) (hp : p.hasSort s) (hq : q.hasSort s)
    (hf : ∀ x ∈ xs, x ∉ p.freeVars ∪ q.freeVars) (R : Assignment)
    (h : ∀ S, S.const = R.const → AgreeOutside xs S R →
      Related Γ Δ s.splitArgs.2
        (S.expression (p.applied (xs.map Expr.var)) (SubstPair.applied_splitArgs_sort s hp xs hx))
        (S.expression (q.applied (xs.map Expr.var)) (SubstPair.applied_splitArgs_sort s hq xs hx))) :
    Related Γ Δ s (R.expression p hp) (R.expression q hq) := by
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
          have hpS : S.expression p hp = R.expression p hp :=
            R.expression_update_fresh x u p hp (fun hm => (hf x (by simp [x])) (by simp [hm]))
          have hqS : S.expression q hq = R.expression q hq :=
            R.expression_update_fresh x u q hq (fun hm => (hf x (by simp [x])) (by simp [hm]))
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
          rw [Assignment.expression_app S (a := .var x) hp rfl,
            Assignment.expression_app S (a := .var x) hq rfl,
            Assignment.expression_var, hpS, hqS] at hd
          have hd' : Related Γ Δ b ((R.expression p hp).app u) ((R.expression q hq).app u) := by
            simpa only [S, Assignment.update_self] using hd
          exact hd'.trans (related_refl (R.expression q hq) u v huv)

/-! Syntactic transport of the generalized simultaneous substitution rule.
The comparison premise is translated uniformly in its fresh parameters. Its
residual contexts are retained; the main premise need not be fresh for them. -/

private theorem fold_and_member (R : Assignment) (hR : R.FixesConstants) (es : List Expr)
    (hs : ∀ e ∈ es, isFormula e) (p : Expr) (hp : p ∈ es) :
    Pure.Provable {R.formula (foldFormulas Expr.and Expr.top es)} {R.formula p} := by
  have go (xs : List Expr) : ∀ a, isFormula a → (∀ e ∈ xs, isFormula e) →
      ∀ q ∈ a :: xs, Pure.Provable {R.formula (xs.foldl Expr.and a)} {R.formula q} := by
    induction xs with
    | nil =>
        intro a _ _ q hq
        have hqa : q = a := by simpa using hq
        subst q
        exact ⟨.hypothesis _⟩
    | cons b bs ih =>
        intro a ha hs q hq
        have hb := hs b (by simp)
        have htail : ∀ e ∈ bs, isFormula e := fun e he => hs e (by simp [he])
        rcases List.mem_cons.mp hq with hqa | hq
        · subst q
          obtain ⟨d⟩ := ih (Expr.and a b) (isFormula_and ha hb) htail (Expr.and a b) (by simp)
          have proj : Pure.ProofTree
              {R.formula (Expr.and a b)} {R.formula a} := by
            rw [R.formula_and hR ha hb]
            exact .leftAnd (Γ := ∅) (R.formula a) (R.formula b)
              (.hypothesisIn (R.formula a) (by simp) (by simp))
          refine ⟨?_⟩
          simpa using Pure.ProofTree.cut (Γ := {R.formula (bs.foldl Expr.and (Expr.and a b))})
            (Δ := ∅) (Θ := ∅) (Ξ := {R.formula a}) (R.formula (Expr.and a b)) d proj
        · rcases List.mem_cons.mp hq with hqb | hq
          · subst q
            obtain ⟨d⟩ := ih (Expr.and a b) (isFormula_and ha hb) htail (Expr.and a b) (by simp)
            have proj : Pure.ProofTree
                {R.formula (Expr.and a b)} {R.formula b} := by
              rw [R.formula_and hR ha hb]
              exact .leftAnd (Γ := ∅) (R.formula a) (R.formula b)
                (.hypothesisIn (R.formula b) (by simp) (by simp))
            refine ⟨?_⟩
            simpa using Pure.ProofTree.cut (Γ := {R.formula (bs.foldl Expr.and (Expr.and a b))})
              (Δ := ∅) (Θ := ∅) (Ξ := {R.formula b}) (R.formula (Expr.and a b)) d proj
          · exact ih (Expr.and a b) (isFormula_and ha hb) htail q (by simp [hq])
  cases es with
  | nil => simp at hp
  | cons a es => exact go es a (hs a (by simp)) (fun e he => hs e (by simp [he])) p hp

private theorem ground_related (R : Assignment) (hR : R.FixesConstants) (s : LSort)
    (hs : s = ind ∨ s = prop) (p q : Expr) (hp : p.hasSort s) (hq : q.hasSort s)
    (h : Pure.Provable Γ (insert (R.formula (if s = prop then Expr.iff p q else Expr.eq p q)) Δ)) :
    Related Γ Δ s (R.expression p hp) (R.expression q hq) := by
  rcases hs with rfl | rfl
  · simp only [if_neg (show ind ≠ prop by decide), R.formula_eq hR hp hq] at h
    exact h
  · simp only [↓reduceIte, R.formula_iff hR hp hq,
      R.formula_of_sorted p hp, R.formula_of_sorted q hq] at h
    exact h

theorem pointwise_related (R : Assignment) (r : SubstPair) (xs : List SVar)
    (hr : r.validParams xs) (s : LSort) (hs : r.source.hasSort s)
    (h : ∀ S, S.const = R.const → AgreeOutside xs S R →
      Pure.Provable Γ (insert (S.formula (r.pointwiseEq xs)) Δ))
    (hR : R.FixesConstants) :
    Related Γ Δ s (R.expression r.source hs) (R.expression r.target (hr.1.2.symm.trans hs)) := by
  have hx : xs.map SVar.sort = s.splitArgs.1 := by
    simpa [SubstPair.sort, show r.source.sort = some s from hs] using hr.2.1
  apply expression_extensional s xs hx hr.2.2.1 r.source r.target hs _ hr.2.2.2 R
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
equivalent. No assumptions on the main premise's contexts occur here. -/
theorem substitution_rule_equiv_contexts (R : Assignment) (hR : R.FixesConstants)
    (r : SubstRule) (hr : r.valid)
    (Θ Ξ : Assignment → Pure.Context Readback.language)
    (fresh : ∀ pair ∈ r.comparisons, ∀ S : Assignment, S.const = R.const →
      AgreeOutside pair.2 S R → Θ S = Θ R ∧ Ξ S = Ξ R)
    (proof : ∀ S : Assignment, S.FixesConstants →
      Pure.Provable (Θ S) (insert (S.formula r.equation) (Ξ S))) :
    Pure.Provable (Θ R)
      (insert (.iff (R.formula r.source) (R.formula r.target)) (Ξ R)) := by
  have each (pair : SubstPair × List SVar) (hm : pair ∈ r.comparisons) :
      RelatedExpr (Θ R) (Ξ R) R pair.1.source pair.1.target := by
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
    simpa using Pure.ProofTree.cut (Δ := Ξ R) (Θ := ∅)
      (Ξ := {S.formula (pair.1.pointwiseEq pair.2)}) (S.formula r.equation) d proj
  have sorts := Instantiation.rule_sorts r hr
  have hs := context_congr R r.context
    (r.comparisons.map (fun pair => pair.1.source))
    (r.comparisons.map (fun pair => pair.1.target))
    sorts.1
    sorts.2 hr.1
    (by
      have go (l : List (SubstPair × List SVar))
          (hh : ∀ pair ∈ l, RelatedExpr (Θ R) (Ξ R) R pair.1.source pair.1.target) :
          List.Forall₂ (RelatedExpr (Θ R) (Ξ R) R)
            (l.map (fun pair => pair.1.source)) (l.map (fun pair => pair.1.target)) := by
        induction l with
        | nil => exact .nil
        | cons pair l ih => exact .cons (hh pair (by simp)) (ih (fun p hp => hh p (by simp [hp])))
      exact go r.comparisons each)
  have hh := (relatedExpr_iff hr.2.2.2.1 hr.2.2.2.2).mp hs
  simpa only [Assignment.formula_of_sorted R r.source hr.2.2.2.1,
    Assignment.formula_of_sorted R r.target hr.2.2.2.2] using hh

end Lisa.SCLambdaToPure.Syntactic

/-! Normalization and first-order readback descend to αβη formula classes. -/
namespace Lisa.SCLambdaToPure.Syntactic.Assignment
open Instantiation

noncomputable def formulaClass (R : Assignment) (p : A.Formula) :
    Pure.Formula Readback.language := R.formula (representative p)

@[simp] theorem formulaClass_ofExpr (R : Assignment) (p : Expr) (hp : isFormula p) :
    R.formulaClass (A.ofExpr p hp) = R.formula p :=
  R.formula_equiv ((A.ofExpr_eq _ _).mp (of_representative (A.ofExpr p hp))) (representative_sort _)

noncomputable def classContext (R : Assignment) (Γ : A.Context) :
    Pure.Context Readback.language := Γ.image R.formulaClass

@[simp] theorem classContext_empty (R : Assignment) : R.classContext ∅ = ∅ := Finset.image_empty _
@[simp] theorem classContext_singleton (R : Assignment) (p : A.Formula) :
    R.classContext {p} = {R.formulaClass p} := Finset.image_singleton _ _
@[simp] theorem classContext_insert (R : Assignment) (p : A.Formula) (Γ : A.Context) :
    R.classContext (insert p Γ) = insert (R.formulaClass p) (R.classContext Γ) := Finset.image_insert _ _ _
@[simp] theorem classContext_union (R : Assignment) (Γ Δ : A.Context) :
    R.classContext (Γ ∪ Δ) = R.classContext Γ ∪ R.classContext Δ := Finset.image_union _ _

theorem classContext_raw (R : Assignment) (Γ : Finset Expr) (hΓ : isFSet Γ) :
    R.classContext (A.context Γ hΓ) = R.context Γ := by
  ext p
  simp only [classContext, context, Finset.mem_image, A.mem_context]
  constructor
  · rintro ⟨q, ⟨e, he, rfl⟩, h⟩
    exact ⟨e, he, by simpa using h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨A.ofExpr e (hΓ e he), ⟨e, he, rfl⟩, by simpa using h⟩

theorem classContext_update_fresh (R : Assignment) (x : SVar) (a : ScopedExpr x.sort)
    (Γ : A.Context) (hf : A.Fresh x Γ) :
    (R.update x a).classContext Γ = R.classContext Γ := by
  apply Finset.image_congr
  intro p hp
  obtain ⟨e, he, rfl, hx⟩ := hf p hp
  simp only [formulaClass_ofExpr, formula_of_sorted _ e he]
  rw [R.expression_update_fresh x a e he hx]

theorem classContext_agreeOutside (R S : Assignment) (xs : List SVar) (Γ : A.Context)
    (hc : S.const = R.const) (hs : AgreeOutside xs S R)
    (hf : ∀ x ∈ xs, A.Fresh x Γ) : S.classContext Γ = R.classContext Γ := by
  induction xs generalizing S with
  | nil =>
      apply Finset.image_congr
      intro p _
      simp only [formulaClass, formula_of_sorted _ _ (representative_sort p)]
      rw [S.expression_support R _ (representative_sort p) hc (fun x _ => hs x (by simp))]
  | cons x xs ih =>
      let U := S.update x (R.free x.sort x.id)
      have hu : AgreeOutside xs U R := by
        intro y hy
        by_cases h : y = x
        · subst y; exact S.update_self x _
        · exact (S.update_other x _ h).trans (hs y (by simp [h, hy]))
      exact (S.classContext_update_fresh x _ Γ (hf x (by simp))).symm.trans
        (ih U hc hu (fun y hy => hf y (by simp [hy])))

end Lisa.SCLambdaToPure.Syntactic.Assignment
