import Lisa.LambdaFol.ToPureFol.NormalizationScope
import Lisa.LambdaFol.ToPureFol.PureFolToOrdered.Embedding
import Lisa.LambdaFol.ToPureFol.PureFolSubstitution

/-! Reify embedded PureFol terms and formulas into named Lisa expressions.
Freshness follows from the named-interpretation roundtrip. Binding and substitution
commute with reification up to alpha-beta-eta equivalence. -/
namespace Lisa.LambdaFol.PureFolEmbedding
open AlphaBetaEtaNormalization
open PureFol (BoundedTerm BoundedFormula)
open PureFolTranslation (language)
open Embedding (apps head mem_apps)
open Signature (arity)

theorem toLambdaFormula_reify_freeVars
    (p : PureFol.Formula language) (ρ : Context) :
    ((toLambdaFormula p).reify ρ).freeVars ⊆ (toLambdaFormula p).freeVars := by
  have h := interpretNamed_freeVars_eq (interpretNamed_reify_free (toLambdaFormula p) ρ)
  simpa only [toLambdaFormula_subst_eq] using h.symm.subset

/-! Named representatives of the independent first-order syntax.
Only individual names are substituted. Individual binders, including epsilon,
commute with the embedding up to alpha equivalence. -/

def toExprFormula (p : PureFol.Formula language) : Expr :=
  (toLambdaFormula p).reify Context.empty
def toExprTerm (t : PureFol.Term language) : Expr :=
  (toLambdaTerm t).reify Context.empty

theorem toExprFormula_sort (p : PureFol.Formula language) :
    isFormula (toExprFormula p) := (toLambdaFormula p).reify_sort _
theorem toExprTerm_sort (t : PureFol.Term language) :
    isTerm (toExprTerm t) := (toLambdaTerm t).reify_sort _

theorem interpret_reifyFormula (p : PureFol.Formula language) :
    interpretNamed (toExprFormula p) Names.free = some ⟨prop, toLambdaFormula p⟩ := by
  simp [toExprFormula, toLambdaFormula_subst_eq]
theorem interpret_reifyTerm (t : PureFol.Term language) :
    interpretNamed (toExprTerm t) Names.free = some ⟨ind, toLambdaTerm t⟩ := by
  simp [toExprTerm, toLambdaTerm_subst_eq]

@[simp] theorem toExprFormula_bot :
    toExprFormula .bot = Expr.bot := rfl
@[simp] theorem toExprFormula_top :
    toExprFormula .top = Expr.top := rfl
@[simp] theorem toExprFormula_not (p : PureFol.Formula language) :
    toExprFormula (.not p) = Expr.neg (toExprFormula p) := rfl
@[simp] theorem toExprFormula_and (p q : PureFol.Formula language) :
    toExprFormula (.and p q) = Expr.and (toExprFormula p) (toExprFormula q) := rfl
@[simp] theorem toExprFormula_or (p q : PureFol.Formula language) :
    toExprFormula (.or p q) = Expr.or (toExprFormula p) (toExprFormula q) := rfl
@[simp] theorem toExprFormula_imp (p q : PureFol.Formula language) :
    toExprFormula (.imp p q) = Expr.imp (toExprFormula p) (toExprFormula q) := rfl
@[simp] theorem toExprFormula_iff (p q : PureFol.Formula language) :
    toExprFormula (.iff p q) = Expr.iff (toExprFormula p) (toExprFormula q) := rfl
@[simp] theorem toExprFormula_equal (t u : PureFol.Term language) :
    toExprFormula (.equal t u) = Expr.eq (toExprTerm t) (toExprTerm u) := rfl

theorem toExprFormula_forall
    (x : Identifier) (p : PureFol.Formula language) :
    AlphaBetaEta (toExprFormula (PureFol.forall_ x p))
      (Expr.forall_ ⟨x, ind⟩ (toExprFormula p)) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyFormula (PureFol.forall_ x p))
  simp [Expr.forall_, interpretNamed, SymbolSubstitution.interpretNamed_bind,
    interpret_reifyFormula, Packed.app, Packed.lam, SymbolSubstitution.packed,
    toLambdaFormula, PureFol.forall_, formula, environment_lift, formula_bind]

theorem toExprFormula_exists
    (x : Identifier) (p : PureFol.Formula language) :
    AlphaBetaEta (toExprFormula (PureFol.exists_ x p))
      (Expr.exists_ ⟨x, ind⟩ (toExprFormula p)) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyFormula (PureFol.exists_ x p))
  simp [Expr.exists_, interpretNamed, SymbolSubstitution.interpretNamed_bind,
    interpret_reifyFormula, Packed.app, Packed.lam, SymbolSubstitution.packed,
    toLambdaFormula, PureFol.exists_, formula, environment_lift, formula_bind]

theorem toExprTerm_epsilon
    (x : Identifier) (p : PureFol.Formula language) :
    AlphaBetaEta (toExprTerm (PureFol.epsilon_ x p))
      (Expr.epsilon_ (.lam ⟨x, ind⟩ (toExprFormula p))) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyTerm (PureFol.epsilon_ x p))
  simp [Expr.epsilon_, interpretNamed, SymbolSubstitution.interpretNamed_bind,
    interpret_reifyFormula, Packed.app, Packed.lam, SymbolSubstitution.packed,
    toLambdaTerm, PureFol.epsilon_, term, environment_lift, formula_bind]

theorem toExprFormula_subst
    (x : Identifier) (t : PureFol.Term language) (p : PureFol.Formula language) :
    AlphaBetaEta (toExprFormula (PureFol.substOne x t p))
      (Expr.substOne ⟨x, ind⟩ (toExprTerm t) (toExprFormula p)) := by
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_reifyFormula (PureFol.substOne x t p))
  rw [interpretNamed_substOne _ _ _ _ _ (interpret_reifyTerm t),
    SymbolSubstitution.interpretNamed_bind, interpret_reifyFormula]
  simp only [Option.map_some, Packed.subst, SymbolSubstitution.packed]
  change some (⟨prop, ((SymbolSubstitution.abstract ⟨x, ind⟩).apply (toLambdaFormula p)).instantiate
    (toLambdaTerm t)⟩ : Packed.Expr) = _
  rw [SymbolSubstitution.instantiate_abstract]
  exact congrArg (fun t => some (⟨prop, t⟩ : Packed.Expr)) (formula_substOne x t p).symm

mutual
  theorem term_free {n : Nat} :
      (t : BoundedTerm language Identifier n) → (x : Identifier) →
      SVar.mk x ind ∈ (term (environment n) t).freeVars → x ∈ t.freeVars
    | .var (.inl y), x, h => by
        have hxy : x = y := congrArg SVar.id (Finset.mem_singleton.mp h)
        simp [BoundedTerm.freeVars, hxy]
    | .var (.inr _), _, h => by simp [term, environment] at h
    | .func c ts, x, h => by
        rcases mem_apps _ _ _ h with h | ⟨i, hi⟩
        · simp at h
        · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, term_free (ts i) x hi⟩
    | .epsilon p, x, h => by
        apply formula_free p x
        simpa [term, environment_lift] using h
  theorem formula_free {n : Nat} :
      (p : BoundedFormula language Identifier n) → (x : Identifier) →
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

theorem toExprFormula_fresh
    (p : PureFol.Formula language) (x : Identifier) (hx : x ∉ p.freeVars) :
    SVar.mk x ind ∉ (toExprFormula p).freeVars :=
  fun h => hx (formula_free p x (toLambdaFormula_reify_freeVars p Context.empty h))

end Lisa.LambdaFol.PureFolEmbedding
