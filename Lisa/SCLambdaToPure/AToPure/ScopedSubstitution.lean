import Lisa.SCLambdaToPure.AToPure.RelatedExpressions
import Lisa.SCLambdaToPure.AToPure.FirstOrderReplacement
import Lisa.SCLambdaToPure.AToPure.ReadbackSubstitution

/-! Individual substitution on complete source expressions commutes with the
first-order reader. This includes substitution underneath epsilon binders. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda
namespace ScopedExpr

def substIndividual (e : ScopedExpr s) (x : Identifier) (a : ScopedExpr ind) : ScopedExpr s where
  term := (Replacement.single ⟨x, ind⟩ a.term).apply e.term
  language := by
    apply e.language.replace
    · intro u n; exact .bound n
    · intro y
      by_cases h : y = x
      · subst y; simpa [Replacement.single] using a.language
      · simpa [Replacement.single, h] using FirstOrderShape.InLanguage.individual y
    · intro y; simpa [Replacement.single] using FirstOrderShape.InLanguage.proposition y
    · intros; rfl
  subst_eq σ := by
    rw [← Replacement.apply_ofSub, Replacement.apply_apply]
    apply Replacement.apply_closed_congr e.term e.subst_eq
    · funext u y
      by_cases h : SVar.mk y u = SVar.mk x ind
      · cases h
        simpa [Replacement.comp, Replacement.single, Replacement.apply_ofSub] using a.subst_eq σ
      · simp only [Replacement.comp, Replacement.single, h, ↓reduceDIte,
          Replacement.apply, Replacement.ofSub]
    · rfl

private theorem normalize_subst (e : ScopedExpr s) (x : Identifier) (a : ScopedExpr ind) :
    normalize (e.substIndividual x a).term =
      normalize ((Replacement.single ⟨x, ind⟩ (normalize a.term)).apply e.term) :=
  normalize_eq_of_equiv (Replacement.single_equiv e.term ⟨x, ind⟩ (normalize_sound a.term))

private theorem normalize_shift (a : ScopedExpr s) (b : LSort) :
    (normalize a.term).shift b = normalize a.term := by
  change (normalize a.term).rename (Ren.shift b) = _
  rw [← Term.subst_ofRen]
  exact normalize_closed a.term a.subst_eq _

theorem readFormula_subst (e : ScopedExpr prop) (x : Identifier) (a : ScopedExpr ind) :
    (e.substIndividual x a).readFormula =
      Pure.substOne x a.readTerm e.readFormula := by
  have hn := FirstOrderShape.normalize_replace_formula
    (FirstOrderShape.preserves_single x (FirstOrderShape.normalize_individual a.language a.subst_eq))
    (FirstOrderShape.normalize_formula e.language e.subst_eq)
  have h := Readback.formula_single e.readFormula_spec x a.readTerm_spec (normalize_shift a ind)
  rw [← hn, ← normalize_subst e x a, (e.substIndividual x a).readFormula_spec] at h
  exact Option.some.inj h

theorem readTerm_subst (e : ScopedExpr ind) (x : Identifier) (a : ScopedExpr ind) :
    (e.substIndividual x a).readTerm =
      e.readTerm.subst (Pure.single x a.readTerm) := by
  have hn := FirstOrderShape.normalize_replace_individual
    (FirstOrderShape.preserves_single x (FirstOrderShape.normalize_individual a.language a.subst_eq))
    (FirstOrderShape.normalize_individual e.language e.subst_eq)
  have h := Readback.term_single e.readTerm_spec x a.readTerm_spec (normalize_shift a ind)
  rw [← hn, ← normalize_subst e x a, (e.substIndividual x a).readTerm_spec] at h
  exact Option.some.inj h

end ScopedExpr
end Lisa.SCLambdaToPure.Syntactic

/-! Ordinary first-order functions preserve provable individual equality.
The argument uses the target substitution rule, so it also covers functions
defined by lambda expressions whose normal forms contain epsilon. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda
open FirstOrderShape (arity)

namespace ScopedExpr
def applied : {n : Nat} → ScopedExpr (arity n s) → (Fin n → ScopedExpr ind) → ScopedExpr s
  | 0, f, _ => f
  | _ + 1, f, a => (f.app (a 0)).applied (fun i => a i.succ)

theorem subst_applied (f : ScopedExpr (arity n s)) (a : Fin n → ScopedExpr ind)
    (x : Identifier) (t : ScopedExpr ind) :
    ((f.applied a).substIndividual x t).term =
      ((f.substIndividual x t).applied (fun i => (a i).substIndividual x t)).term := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (f.app (a 0)) (fun i => a i.succ)

theorem subst_fresh (e : ScopedExpr s) (x : Identifier) (t : ScopedExpr ind)
    (hx : SVar.mk x ind ∉ e.term.freeVars) :
    (e.substIndividual x t).term = e.term :=
  Replacement.single_fresh e.term ⟨x, ind⟩ t.term hx

@[ext] theorem ext {e f : ScopedExpr s} (h : e.term = f.term) : e = f := by
  cases e; cases f; cases h; rfl

end ScopedExpr

theorem related_ground_refl (hs : s = ind ∨ s = prop) (e : ScopedExpr s) : Related Γ Δ s e e := by
  rcases hs with rfl | rfl
  · exact ⟨.reflexive _⟩
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
    (f : ScopedExpr (ind >> arity n s)) (args : Fin n → ScopedExpr ind)
    {a b : ScopedExpr ind} (hab : Related Γ Δ ind a b) :
    Related Γ Δ s ((f.app a).applied args) ((f.app b).applied args) := by
  let left := (f.app a).applied args
  let vs := f.term.freeVars ∪ Finset.univ.biUnion (fun i => (args i).term.freeVars)
  let ns : Finset Identifier := match s, left with
    | .ind, e => e.readTerm.freeVars
    | _, _ => ∅
  obtain ⟨x, hx, hn⟩ := fresh_individual vs ns
  have hxf : SVar.mk x ind ∉ f.term.freeVars := fun h => hx (Finset.mem_union_left _ h)
  have hxa : ∀ i, SVar.mk x ind ∉ (args i).term.freeVars := by
    intro i hi
    exact hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩))
  let context := (f.app (ScopedExpr.individual x)).applied args
  have replace (t : ScopedExpr ind) : context.substIndividual x t = (f.app t).applied args := by
    apply ScopedExpr.ext
    rw [ScopedExpr.subst_applied]
    have hf : (f.app (ScopedExpr.individual x)).substIndividual x t = f.app t := by
      apply ScopedExpr.ext
      change Term.app ((Replacement.single ⟨x, ind⟩ t.term).apply f.term)
        ((Replacement.single ⟨x, ind⟩ t.term).apply (.free x)) = _
      rw [Replacement.single_fresh f.term _ _ hxf]
      simp [Replacement.apply, Replacement.single, ScopedExpr.app]
    have ha : (fun i => (args i).substIndividual x t) = args :=
      funext (fun i => ScopedExpr.ext ((args i).subst_fresh x t (hxa i)))
    rw [hf, ha]
  obtain ⟨d⟩ := hab
  rcases hs with rfl | rfl
  · have he (t : ScopedExpr ind) := context.readTerm_subst x t
    have hleft : x ∉ left.readTerm.freeVars := hn
    have initial : Pure.ProofTree ∅
        {Pure.substOne x a.readTerm
          (.equal left.readTerm context.readTerm)} := by
      simpa [Pure.substOne, Pure.BFormula.subst,
        left.readTerm.subst_single_fresh a.readTerm hleft, ← he, replace, left] using
        (Pure.ProofTree.refl left.readTerm)
    have result := Pure.ProofTree.rightSubst (Γ := ∅) (Δ := ∅)
      x (.equal left.readTerm context.readTerm) a.readTerm b.readTerm initial d
    refine ⟨?_⟩
    simpa [Pure.substOne, Pure.BFormula.subst,
      left.readTerm.subst_single_fresh b.readTerm hleft, ← he, replace, left] using result
  · have he (t : ScopedExpr ind) := context.readFormula_subst x t
    refine ⟨?_⟩
    simpa [← he, replace] using d.subst_iff x context.readFormula a.readTerm b.readTerm

/-- A pointwise comparison on identical individual arguments determines the
relation on first-order function types. Equality substitution supplies the
change from identical to related arguments. -/
theorem related_firstOrder (hs : s = ind ∨ s = prop) (f g : ScopedExpr (arity n s))
    (h : ∀ args, Related Γ Δ s (f.applied args) (g.applied args)) :
    Related Γ Δ (arity n s) f g := by
  induction n with
  | zero => exact h Fin.elim0
  | succ n ih =>
      intro a b hab
      apply ih (f.app a) (g.app b)
      intro args
      exact (related_argument hs f args hab).trans (h (Fin.cons b args))

theorem related_firstOrder_refl (hs : s = ind ∨ s = prop) (f : ScopedExpr (arity n s)) :
    Related Γ Δ (arity n s) f f :=
  related_firstOrder hs f f (fun _ => related_ground_refl hs _)

end Lisa.SCLambdaToPure.Syntactic
