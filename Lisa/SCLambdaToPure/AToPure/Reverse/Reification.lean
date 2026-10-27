import Lisa.SCLambdaToPure.AToPure.Normalization
import Lisa.SCLambdaToPure.AToPure.Reverse.Embedding
import Lisa.SCLambdaToPure.AToPure.PureOperations

/-! Reify embedded Pure terms and formulas into named Lisa expressions.
Freshness follows from the named-interpretation roundtrip. Binding and substitution
commute with reification up to alpha-beta-eta equivalence. -/
namespace Lisa.SCLambdaToPure.PureEmbedding
open Lambda
open Pure (BTerm BFormula)
open Readback (language)
open Embedding (apps head mem_apps)
open Signature (arity)

theorem ofFormula_reify_freeVars
    (p : Pure.Formula language) (ρ : Context) :
    ((ofFormula p).reify ρ).freeVars ⊆ (ofFormula p).freeVars := by
  have h := interpretNamed_freeVars_eq (interpretNamed_reify_free (ofFormula p) ρ)
  simpa only [ofFormula_subst_eq] using h.symm.subset

theorem ofTerm_reify_freeVars
    (t : Pure.Term language) (ρ : Context) :
    ((ofTerm t).reify ρ).freeVars ⊆ (ofTerm t).freeVars := by
  have h := interpretNamed_freeVars_eq (interpretNamed_reify_free (ofTerm t) ρ)
  simpa only [ofTerm_subst_eq] using h.symm.subset

/-! Named representatives of the independent first-order syntax.
Only individual names are substituted. Individual binders, including epsilon,
commute with the embedding up to alpha equivalence. -/

def reifyFormula (p : Pure.Formula language) : Expr :=
  (ofFormula p).reify Context.empty
def reifyTerm (t : Pure.Term language) : Expr :=
  (ofTerm t).reify Context.empty

theorem reifyFormula_sort (p : Pure.Formula language) :
    isFormula (reifyFormula p) := (ofFormula p).reify_sort _
theorem reifyTerm_sort (t : Pure.Term language) :
    isTerm (reifyTerm t) := (ofTerm t).reify_sort _

theorem interpret_reifyFormula (p : Pure.Formula language) :
    interpretNamed (reifyFormula p) Names.free = some ⟨prop, ofFormula p⟩ := by
  simp [reifyFormula, ofFormula_subst_eq]
theorem interpret_reifyTerm (t : Pure.Term language) :
    interpretNamed (reifyTerm t) Names.free = some ⟨ind, ofTerm t⟩ := by
  simp [reifyTerm, ofTerm_subst_eq]

@[simp] theorem reifyFormula_bot :
    reifyFormula .bot = Expr.bot := rfl
@[simp] theorem reifyFormula_top :
    reifyFormula .top = Expr.top := rfl
@[simp] theorem reifyFormula_not (p : Pure.Formula language) :
    reifyFormula (.not p) = Expr.neg (reifyFormula p) := rfl
@[simp] theorem reifyFormula_and (p q : Pure.Formula language) :
    reifyFormula (.and p q) = Expr.and (reifyFormula p) (reifyFormula q) := rfl
@[simp] theorem reifyFormula_or (p q : Pure.Formula language) :
    reifyFormula (.or p q) = Expr.or (reifyFormula p) (reifyFormula q) := rfl
@[simp] theorem reifyFormula_imp (p q : Pure.Formula language) :
    reifyFormula (.imp p q) = Expr.imp (reifyFormula p) (reifyFormula q) := rfl
@[simp] theorem reifyFormula_iff (p q : Pure.Formula language) :
    reifyFormula (.iff p q) = Expr.iff (reifyFormula p) (reifyFormula q) := rfl
@[simp] theorem reifyFormula_equal (t u : Pure.Term language) :
    reifyFormula (.equal t u) = Expr.eq (reifyTerm t) (reifyTerm u) := rfl

theorem reifyFormula_forall
    (x : Identifier) (p : Pure.Formula language) :
    AlphaBetaEta (reifyFormula (Pure.forall_ x p))
      (Expr.forall_ ⟨x, ind⟩ (reifyFormula p)) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyFormula (Pure.forall_ x p))
  simp [Expr.forall_, interpretNamed, Replacement.interpretNamed_bind,
    interpret_reifyFormula, Packed.app, Packed.lam, Replacement.packed,
    ofFormula, Pure.forall_, formula, environment_lift, formula_bind]

theorem reifyFormula_exists
    (x : Identifier) (p : Pure.Formula language) :
    AlphaBetaEta (reifyFormula (Pure.exists_ x p))
      (Expr.exists_ ⟨x, ind⟩ (reifyFormula p)) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyFormula (Pure.exists_ x p))
  simp [Expr.exists_, interpretNamed, Replacement.interpretNamed_bind,
    interpret_reifyFormula, Packed.app, Packed.lam, Replacement.packed,
    ofFormula, Pure.exists_, formula, environment_lift, formula_bind]

theorem reifyTerm_epsilon
    (x : Identifier) (p : Pure.Formula language) :
    AlphaBetaEta (reifyTerm (Pure.epsilon_ x p))
      (Expr.epsilon_ (.lam ⟨x, ind⟩ (reifyFormula p))) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyTerm (Pure.epsilon_ x p))
  simp [Expr.epsilon_, interpretNamed, Replacement.interpretNamed_bind,
    interpret_reifyFormula, Packed.app, Packed.lam, Replacement.packed,
    ofTerm, Pure.epsilon_, term, environment_lift, formula_bind]

theorem reifyFormula_subst
    (x : Identifier) (t : Pure.Term language) (p : Pure.Formula language) :
    AlphaBetaEta (reifyFormula (Pure.substOne x t p))
      (Expr.substOne ⟨x, ind⟩ (reifyTerm t) (reifyFormula p)) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyFormula (Pure.substOne x t p))
  rw [interpretNamed_substOne _ _ _ _ _ (interpret_reifyTerm t),
    Replacement.interpretNamed_bind, interpret_reifyFormula]
  simp only [Option.map_some, Packed.subst, Replacement.packed]
  change some (⟨prop, ((Replacement.abstract ⟨x, ind⟩).apply (ofFormula p)).instantiate
    (ofTerm t)⟩ : Packed.Expr) = _
  rw [Replacement.instantiate_abstract]
  exact congrArg (fun t => some (⟨prop, t⟩ : Packed.Expr)) (formula_substOne x t p).symm

mutual
  theorem term_free {n : Nat} :
      (t : BTerm language Identifier n) → (x : Identifier) →
      SVar.mk x ind ∈ (term (environment n) t).freeVars → x ∈ t.freeVars
    | .var (.inl y), x, h => by
        have hxy : x = y := congrArg SVar.id (Finset.mem_singleton.mp h)
        simp [BTerm.freeVars, hxy]
    | .var (.inr _), _, h => by simp [term, environment] at h
    | .func c ts, x, h => by
        rcases mem_apps _ _ _ h with h | ⟨i, hi⟩
        · simp at h
        · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, term_free (ts i) x hi⟩
    | .epsilon p, x, h => by
        apply formula_free p x
        simpa [term, environment_lift] using h
  theorem formula_free {n : Nat} :
      (p : BFormula language Identifier n) → (x : Identifier) →
      SVar.mk x ind ∈ (formula (environment n) p).freeVars → x ∈ p.freeVars
    | .rel (k := k) c ts, x, h => by
        rcases mem_apps _ _ _ h with h | ⟨i, hi⟩
        · have hs : arity k prop ≠ ind := by cases k <;> simp [arity]
          simp only [head] at h
          split at h
          · exact False.elim (hs (congrArg SVar.sort (Finset.mem_singleton.mp h)).symm)
          · simp at h
        · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, term_free (ts i) x hi⟩
    | .equal t u, x, h => by
        simp only [formula, Term.freeVars, Finset.empty_union, Finset.mem_union] at h
        exact h.elim (fun h => Finset.mem_union_left _ (term_free t x h))
          (fun h => Finset.mem_union_right _ (term_free u x h))
    | .top, _, h | .bot, _, h => by simp [formula] at h
    | .not p, x, h => formula_free p x (by simpa [formula] using h)
    | .and p q, x, h | .or p q, x, h | .imp p q, x, h | .iff p q, x, h => by
        simp only [formula, Term.freeVars, Finset.empty_union, Finset.mem_union] at h
        exact h.elim (fun h => Finset.mem_union_left _ (formula_free p x h))
          (fun h => Finset.mem_union_right _ (formula_free q x h))
    | .all p, x, h | .ex p, x, h => by
        apply formula_free p x
        simpa [formula, environment_lift] using h
end

theorem reifyFormula_fresh
    (p : Pure.Formula language) (x : Identifier) (hx : x ∉ p.freeVars) :
    SVar.mk x ind ∉ (reifyFormula p).freeVars :=
  fun h => hx (formula_free p x (ofFormula_reify_freeVars p Context.empty h))

end Lisa.SCLambdaToPure.PureEmbedding
