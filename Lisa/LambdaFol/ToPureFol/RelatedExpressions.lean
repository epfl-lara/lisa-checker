import Lisa.LambdaFol.ToPureFol.DefaultAssignment
import Lisa.LambdaFol.ToPureFol.PureFolDerivedRules

/-! Why replacing related expressions preserves provability.
At individual sort the relation is provable equality; at proposition sort it
is provable equivalence. At function sorts it preserves related arguments.
The syntax induction `apply_preserves_related` reduces the proof to source symbols;
the remaining lemmas verify the first-order and logical symbols. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization.Algorithm

/-- Relate syntax using derivations at ground sorts and applications at arrow sorts. -/
def ProvablyRelated (Γ Δ : Finset (PureFol.Formula PureFolTranslation.language)) :
    (s : LSort) → FirstOrderCompatibleExpr s → FirstOrderCompatibleExpr s → Prop
  | .ind, e, f => PureFol.Provable Γ (insert (.equal e.toPureFolTerm f.toPureFolTerm) Δ)
  | .prop, e, f => PureFol.Provable Γ (insert (.iff e.toPureFolFormula f.toPureFolFormula) Δ)
  | .arrow s t, e, f => ∀ a b, ProvablyRelated Γ Δ s a b → ProvablyRelated Γ Δ t (e.app a) (f.app b)

theorem ProvablyRelated.convert {e e' f f' : FirstOrderCompatibleExpr s}
    (he : Equiv e.term e'.term) (hf : Equiv f.term f'.term)
    (h : ProvablyRelated Γ Δ s e f) : ProvablyRelated Γ Δ s e' f' := by
  induction s with
  | ind => simpa only [ProvablyRelated, FirstOrderCompatibleExpr.toPureFolTerm_equiv he, FirstOrderCompatibleExpr.toPureFolTerm_equiv hf] using h
  | prop => simpa only [ProvablyRelated, FirstOrderCompatibleExpr.toPureFolFormula_equiv he, FirstOrderCompatibleExpr.toPureFolFormula_equiv hf] using h
  | arrow s t ihs iht =>
      intro a b hab
      exact iht (.app he (.refl _)) (.app hf (.refl _)) (h a b hab)

private theorem related_symmetric_transitive (s : LSort) :
    (∀ e f, ProvablyRelated Γ Δ s e f → ProvablyRelated Γ Δ s f e) ∧
    (∀ e f g, ProvablyRelated Γ Δ s e f → ProvablyRelated Γ Δ s f g → ProvablyRelated Γ Δ s e g) := by
  induction s with
  | ind =>
      constructor
      · intro e f ⟨d⟩; exact ⟨d.eq_symm⟩
      · intro e f g ⟨d⟩ ⟨h⟩; exact ⟨d.eq_trans h⟩
  | prop =>
      constructor
      · intro e f ⟨d⟩; exact ⟨d.iff_symm⟩
      · intro e f g ⟨d⟩ ⟨h⟩; exact ⟨d.iff_trans h⟩
  | arrow s t ihs iht =>
      constructor
      · intro e f h a b hab
        exact iht.1 _ _ (h b a (ihs.1 _ _ hab))
      · intro e f g h₁ h₂ a b hab
        have hbb := ihs.2 _ _ _ (ihs.1 _ _ hab) hab
        exact iht.2 _ _ _ (h₁ a b hab) (h₂ b b hbb)

theorem ProvablyRelated.trans {e f g : FirstOrderCompatibleExpr s}
    (h : ProvablyRelated Γ Δ s e f) (h' : ProvablyRelated Γ Δ s f g) : ProvablyRelated Γ Δ s e g :=
  (related_symmetric_transitive s).2 _ _ _ h h'

structure ProvablyRelatedAssignments (Γ Δ : Finset (PureFol.Formula PureFolTranslation.language))
    (R S : FirstOrderAssignment) : Prop where
  bound : ∀ s n, ProvablyRelated Γ Δ s (R.bound s n) (S.bound s n)
  free : ∀ s x, ProvablyRelated Γ Δ s (R.free s x) (S.free s x)
  const : ∀ s c, ProvablyRelated Γ Δ s (R.const s c) (S.const s c)

theorem ProvablyRelatedAssignments.extend (h : ProvablyRelatedAssignments Γ Δ R S)
    (ha : ProvablyRelated Γ Δ s a b) : ProvablyRelatedAssignments Γ Δ (R.extend a) (S.extend b) where
  bound u n := by
    by_cases hu : u = s
    · subst u; cases n
      · simpa only [FirstOrderAssignment.extend_zero] using ha
      · simpa only [FirstOrderAssignment.extend_succ] using h.bound s _
    · simpa only [FirstOrderAssignment.extend_other _ _ hu] using h.bound u n
  free := h.free
  const := h.const

/-- Assigning related expressions to source symbols produces related expressions.
The proof follows lambda syntax, extending the assignments under each binder. -/
theorem apply_preserves_related (e : Term s) (h : ProvablyRelatedAssignments Γ Δ R S) :
    ProvablyRelated Γ Δ s (R.apply e) (S.apply e) := by
  induction e generalizing R S with
  | bound n => exact h.bound _ n
  | free x => exact h.free _ x
  | const c => exact h.const _ c
  | app f a ihf iha => exact ihf h _ _ (iha h)
  | lam b e ih =>
      intro a a' ha
      exact ProvablyRelated.convert (R.apply_lam e a).symm (S.apply_lam e a').symm
        (ih (h.extend ha))

theorem related_neg : ProvablyRelated Γ Δ (prop >> prop)
    (FirstOrderCompatibleExpr.constant _ .neg) (FirstOrderCompatibleExpr.constant _ .neg) := by
  intro p q ⟨h⟩
  simpa only [ProvablyRelated, ← FirstOrderCompatibleExpr.neg.eq_1, FirstOrderCompatibleExpr.toPureFolFormula_neg] using
    (show PureFol.Provable Γ _ from ⟨h.not_congr⟩)

theorem related_and : ProvablyRelated Γ Δ (prop >> prop >> prop)
    (FirstOrderCompatibleExpr.constant _ .and) (FirstOrderCompatibleExpr.constant _ .and) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [ProvablyRelated, ← FirstOrderCompatibleExpr.and.eq_1, FirstOrderCompatibleExpr.toPureFolFormula_and] using
    (show PureFol.Provable Γ _ from ⟨hp.and_congr hq⟩)

theorem related_or : ProvablyRelated Γ Δ (prop >> prop >> prop)
    (FirstOrderCompatibleExpr.constant _ .or) (FirstOrderCompatibleExpr.constant _ .or) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [ProvablyRelated, ← FirstOrderCompatibleExpr.or.eq_1, FirstOrderCompatibleExpr.toPureFolFormula_or] using
    (show PureFol.Provable Γ _ from ⟨hp.or_congr hq⟩)

theorem related_imp : ProvablyRelated Γ Δ (prop >> prop >> prop)
    (FirstOrderCompatibleExpr.constant _ .imp) (FirstOrderCompatibleExpr.constant _ .imp) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [ProvablyRelated, ← FirstOrderCompatibleExpr.imp.eq_1, FirstOrderCompatibleExpr.toPureFolFormula_imp] using
    (show PureFol.Provable Γ _ from ⟨hp.imp_congr hq⟩)

theorem related_iff : ProvablyRelated Γ Δ (prop >> prop >> prop)
    (FirstOrderCompatibleExpr.constant _ .iff) (FirstOrderCompatibleExpr.constant _ .iff) := by
  intro p p' ⟨hp⟩ q q' ⟨hq⟩
  simpa only [ProvablyRelated, ← FirstOrderCompatibleExpr.iff.eq_1, FirstOrderCompatibleExpr.toPureFolFormula_iff] using
    (show PureFol.Provable Γ _ from ⟨hp.iff_congr hq⟩)

-- First-order functions preserve individual equality by PureFol's substitution rule.
open FirstOrderShape (arity)

namespace FirstOrderCompatibleExpr
def applied : {n : Nat} → FirstOrderCompatibleExpr (arity n s) → (Fin n → FirstOrderCompatibleExpr ind) → FirstOrderCompatibleExpr s
  | 0, f, _ => f
  | _ + 1, f, a => (f.app (a 0)).applied (fun i => a i.succ)

theorem subst_applied (f : FirstOrderCompatibleExpr (arity n s)) (a : Fin n → FirstOrderCompatibleExpr ind)
    (x : Identifier) (t : FirstOrderCompatibleExpr ind) :
    ((f.applied a).substIndividual x t).term =
      ((f.substIndividual x t).applied (fun i => (a i).substIndividual x t)).term := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (f.app (a 0)) (fun i => a i.succ)

theorem subst_fresh (e : FirstOrderCompatibleExpr s) (x : Identifier) (t : FirstOrderCompatibleExpr ind)
    (hx : SVar.mk x ind ∉ e.term.freeVars) :
    (e.substIndividual x t).term = e.term :=
  SymbolSubstitution.single_fresh e.term ⟨x, ind⟩ t.term hx

end FirstOrderCompatibleExpr

theorem related_ground_refl (hs : s = ind ∨ s = prop) (e : FirstOrderCompatibleExpr s) : ProvablyRelated Γ Δ s e e := by
  rcases hs with rfl | rfl
  · exact ⟨.eq_refl _⟩
  · exact ⟨.iff_refl _⟩

private theorem fresh_individual (vs : Finset SVar) (ns : Finset Identifier) :
    ∃ x : Identifier, SVar.mk x ind ∉ vs ∧ x ∉ ns := by
  let blocked := vs.image (fun v => v.id) ∪ ns
  let x := freshId blocked ⟨"_eigen", 0⟩
  have hx : x ∉ blocked := freshId_not_mem _ _
  refine ⟨x, ?_, ?_⟩
  · intro h
    exact hx (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨x, ind⟩, h, rfl⟩))
  · intro h; exact hx (Finset.mem_union_right _ h)

private theorem related_argument (hs : s = ind ∨ s = prop)
    (f : FirstOrderCompatibleExpr (ind >> arity n s)) (args : Fin n → FirstOrderCompatibleExpr ind)
    {a b : FirstOrderCompatibleExpr ind} (hab : ProvablyRelated Γ Δ ind a b) :
    ProvablyRelated Γ Δ s ((f.app a).applied args) ((f.app b).applied args) := by
  let left := (f.app a).applied args
  let vs := f.term.freeVars ∪ Finset.univ.biUnion (fun i => (args i).term.freeVars)
  let ns : Finset Identifier := match s, left with
    | .ind, e => e.toPureFolTerm.freeVars
    | _, _ => ∅
  obtain ⟨x, hx, hn⟩ := fresh_individual vs ns
  have hxf : SVar.mk x ind ∉ f.term.freeVars := fun h => hx (Finset.mem_union_left _ h)
  have hxa : ∀ i, SVar.mk x ind ∉ (args i).term.freeVars := by
    intro i hi
    exact hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩))
  let body := (f.app (FirstOrderCompatibleExpr.individual x)).applied args
  have replace (t : FirstOrderCompatibleExpr ind) : body.substIndividual x t = (f.app t).applied args := by
    apply FirstOrderCompatibleExpr.ext
    rw [FirstOrderCompatibleExpr.subst_applied]
    have hf : (f.app (FirstOrderCompatibleExpr.individual x)).substIndividual x t = f.app t := by
      apply FirstOrderCompatibleExpr.ext
      change Term.app ((SymbolSubstitution.single ⟨x, ind⟩ t.term).apply f.term)
        ((SymbolSubstitution.single ⟨x, ind⟩ t.term).apply (.free x)) = _
      rw [SymbolSubstitution.single_fresh f.term _ _ hxf]
      simp [SymbolSubstitution.apply, SymbolSubstitution.single, FirstOrderCompatibleExpr.app]
    have ha : (fun i => (args i).substIndividual x t) = args :=
      funext (fun i => FirstOrderCompatibleExpr.ext ((args i).subst_fresh x t (hxa i)))
    rw [hf, ha]
  obtain ⟨d⟩ := hab
  rcases hs with rfl | rfl
  · have he (t : FirstOrderCompatibleExpr ind) := body.toPureFolTerm_subst x t
    have hleft : x ∉ left.toPureFolTerm.freeVars := hn
    have initial : PureFol.ProofTree ∅
        {PureFol.substOne x a.toPureFolTerm
          (.equal left.toPureFolTerm body.toPureFolTerm)} := by
      simpa [PureFol.substOne, PureFol.BoundedFormula.subst,
        left.toPureFolTerm.subst_single_fresh a.toPureFolTerm hleft, ← he, replace, left] using
        (PureFol.ProofTree.refl left.toPureFolTerm)
    have result := PureFol.ProofTree.rightSubst (Γ := ∅) (Δ := ∅)
      x (.equal left.toPureFolTerm body.toPureFolTerm) a.toPureFolTerm b.toPureFolTerm initial d
    refine ⟨?_⟩
    simpa [PureFol.substOne, PureFol.BoundedFormula.subst,
      left.toPureFolTerm.subst_single_fresh b.toPureFolTerm hleft, ← he, replace, left] using result
  · have he (t : FirstOrderCompatibleExpr ind) := body.toPureFolFormula_subst x t
    refine ⟨?_⟩
    simpa [← he, replace] using d.subst_iff x body.toPureFolFormula a.toPureFolTerm b.toPureFolTerm

/-- A pointwise comparison on identical individual arguments determines the
relation on first-order function types. Equality substitution supplies the
change from identical to related arguments. -/
theorem related_firstOrder (hs : s = ind ∨ s = prop) (f g : FirstOrderCompatibleExpr (arity n s))
    (h : ∀ args, ProvablyRelated Γ Δ s (f.applied args) (g.applied args)) :
    ProvablyRelated Γ Δ (arity n s) f g := by
  induction n with
  | zero => exact h Fin.elim0
  | succ n ih =>
      intro a b hab
      apply ih (f.app a) (g.app b)
      intro args
      exact (related_argument hs f args hab).trans (h (Fin.cons b args))

theorem related_firstOrder_refl (hs : s = ind ∨ s = prop) (f : FirstOrderCompatibleExpr (arity n s)) :
    ProvablyRelated Γ Δ (arity n s) f f :=
  related_firstOrder hs f f (fun _ => related_ground_refl hs _)

theorem related_all : ProvablyRelated Γ Δ ((ind >> prop) >> prop)
    (FirstOrderCompatibleExpr.constant _ .all) (FirstOrderCompatibleExpr.constant _ .all) := by
  intro f g h
  obtain ⟨x, hxf, hxg, hΓ, hΔ⟩ := freshForBinders f g Γ Δ
  obtain ⟨d⟩ := h (FirstOrderCompatibleExpr.individual x) (FirstOrderCompatibleExpr.individual x) ⟨.eq_refl _⟩
  change PureFol.Provable Γ (insert (.iff (FirstOrderCompatibleExpr.all f).toPureFolFormula
    (FirstOrderCompatibleExpr.all g).toPureFolFormula) Δ)
  rw [FirstOrderCompatibleExpr.toPureFolFormula_all f x hxf,
    FirstOrderCompatibleExpr.toPureFolFormula_all g x hxg]
  exact ⟨d.forall_congr x hΓ hΔ⟩

theorem related_ex : ProvablyRelated Γ Δ ((ind >> prop) >> prop)
    (FirstOrderCompatibleExpr.constant _ .ex) (FirstOrderCompatibleExpr.constant _ .ex) := by
  intro f g h
  obtain ⟨x, hxf, hxg, hΓ, hΔ⟩ := freshForBinders f g Γ Δ
  obtain ⟨d⟩ := h (FirstOrderCompatibleExpr.individual x) (FirstOrderCompatibleExpr.individual x) ⟨.eq_refl _⟩
  change PureFol.Provable Γ (insert (.iff (FirstOrderCompatibleExpr.ex f).toPureFolFormula
    (FirstOrderCompatibleExpr.ex g).toPureFolFormula) Δ)
  rw [FirstOrderCompatibleExpr.toPureFolFormula_ex f x hxf,
    FirstOrderCompatibleExpr.toPureFolFormula_ex g x hxg]
  exact ⟨d.exists_congr x hΓ hΔ⟩

theorem related_epsilon : ProvablyRelated Γ Δ ((ind >> prop) >> ind)
    (FirstOrderCompatibleExpr.constant _ .epsilon) (FirstOrderCompatibleExpr.constant _ .epsilon) := by
  intro f g h
  obtain ⟨x, hxf, hxg, hΓ, hΔ⟩ := freshForBinders f g Γ Δ
  obtain ⟨d⟩ := h (FirstOrderCompatibleExpr.individual x) (FirstOrderCompatibleExpr.individual x) ⟨.eq_refl _⟩
  change PureFol.Provable Γ (insert (.equal (FirstOrderCompatibleExpr.epsilon f).toPureFolTerm
    (FirstOrderCompatibleExpr.epsilon g).toPureFolTerm) Δ)
  rw [FirstOrderCompatibleExpr.toPureFolTerm_epsilon f x hxf,
    FirstOrderCompatibleExpr.toPureFolTerm_epsilon g x hxg]
  exact ⟨PureFol.ProofTree.epsilonExt x _ _ d hΓ hΔ⟩

-- Every allowed symbol, and hence every complete expression, respects the relation.
theorem related_constant (h : FirstOrderShape.AllowedConstant s c) :
    ProvablyRelated Γ Δ s (FirstOrderCompatibleExpr.constant c h) (FirstOrderCompatibleExpr.constant c h) := by
  cases h with
  | function n c => exact related_firstOrder_refl (Or.inl rfl) _
  | predicate n c => exact related_firstOrder_refl (Or.inr rfl) _
  | neg => exact related_neg
  | and => exact related_and
  | or => exact related_or
  | imp => exact related_imp
  | iff => exact related_iff
  | all => exact related_all
  | ex => exact related_ex
  | epsilon => exact related_epsilon

theorem related_default (s : LSort) : ProvablyRelated Γ Δ s (FirstOrderCompatibleExpr.default s) (FirstOrderCompatibleExpr.default s) := by
  induction s with
  | ind => exact related_ground_refl (Or.inl rfl) _
  | prop => exact related_ground_refl (Or.inr rfl) _
  | arrow s t _ ih =>
      intro a b _
      exact ProvablyRelated.convert (FirstOrderCompatibleExpr.constantFunction_apply s _ a).symm
        (FirstOrderCompatibleExpr.constantFunction_apply s _ b).symm ih

namespace FirstOrderAssignment

theorem defaultAssignment_related : ProvablyRelatedAssignments Γ Δ defaultAssignment defaultAssignment where
  bound s _ := related_default s
  free := by
    intro s x; cases s with
    | ind => exact related_ground_refl (Or.inl rfl) _
    | prop => exact related_ground_refl (Or.inr rfl) _
    | arrow _ _ => exact related_default _
  const := by
    intro s c
    by_cases h : FirstOrderShape.AllowedConstant s c
    · simpa only [defaultAssignment, h, ↓reduceDIte] using related_constant (Γ := Γ) (Δ := Δ) h
    · simpa only [defaultAssignment, h, ↓reduceDIte] using related_default (Γ := Γ) (Δ := Δ) s

end FirstOrderAssignment

/-- Every first-order-compatible expression respects provable equality and
equivalence. Arrow sorts use related arguments, not higher-order equality in
the target language. -/
theorem related_refl (e : FirstOrderCompatibleExpr s) : ProvablyRelated Γ Δ s e e := by
  simpa only [FirstOrderAssignment.defaultAssignment_apply] using
    apply_preserves_related e.term (FirstOrderAssignment.defaultAssignment_related (Γ := Γ) (Δ := Δ))

end Lisa.LambdaFol
