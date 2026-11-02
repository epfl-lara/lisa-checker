import Lisa.LambdaFol.EliminateInstantiation.InstantiateRuleData
import Lisa.LambdaFol.EliminateInstantiation.Conjunction
/-! The generalized replacement rule survives schematic instantiation.
Each comparison is first projected from its premise with its own fresh parameter
renaming; the resulting comparisons are then conjoined again. -/
noncomputable section
namespace Lisa.LambdaFol
open Expr

namespace Instantiation

theorem apply_andFold (σ : Instantiation) (es : List Expr) (p : Expr) :
    σ.apply (es.foldl Expr.and p) = (es.map σ.apply).foldl Expr.and (σ.apply p) := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih => exact ih (and p e)

theorem apply_conjunction (σ : Instantiation) (es : List Expr) :
    σ.apply (foldFormulas Expr.and top es) = foldFormulas Expr.and top (es.map σ.apply) := by
  cases es with
  | nil => rfl
  | cons e es => exact apply_andFold σ es e

/-- Names excluded when freshening one replacement rule. -/
def replacementForbiddenNames (σ : Instantiation) (r : SubstRule) (Θ Ξ : Finset LambdaFol.Formula) : Finset SVar := by
  classical
  exact (σ.substitution.rangeFreeVars ∪ r.context.body.freeVars) ∪
    r.comparisons.toFinset.biUnion (fun c => (σ.apply c.1.source).freeVars ∪ (σ.apply c.1.target).freeVars) ∪
    (representativeFreeVars (σ.formulaSet Θ) ∪ representativeFreeVars (σ.formulaSet Ξ))

theorem replacementForbiddenNames_context (σ : Instantiation) (r : SubstRule) (Θ Ξ : Finset LambdaFol.Formula) (x : SVar) :
    freshParameters (replacementForbiddenNames σ r Θ Ξ) x ∉ σ.substitution.rangeFreeVars ∪ r.context.body.freeVars := by
  intro h
  exact freshParameters_fresh _ x (Finset.mem_union_left _ (Finset.mem_union_left _ h))

theorem replacementForbiddenNames_comparison (σ : Instantiation) (r : SubstRule) (Θ Ξ : Finset LambdaFol.Formula)
    (c : SubstPair × List SVar) (hc : c ∈ r.comparisons) (x : SVar) :
    freshParameters (replacementForbiddenNames σ r Θ Ξ) x ∉ (σ.apply c.1.source).freeVars ∪ (σ.apply c.1.target).freeVars := by
  intro h
  exact freshParameters_fresh _ x (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, by simpa using hc, h⟩)))

theorem replacementForbiddenNames_fresh (σ : Instantiation) (r : SubstRule) (Θ Ξ : Finset LambdaFol.Formula) (x : SVar) :
    LambdaFol.Fresh (freshParameters (replacementForbiddenNames σ r Θ Ξ) x) (σ.formulaSet Θ) ∧
    LambdaFol.Fresh (freshParameters (replacementForbiddenNames σ r Θ Ξ) x) (σ.formulaSet Ξ) := by
  constructor
  · exact fresh_of_not_mem_support (fun h => freshParameters_fresh _ x
      (Finset.mem_union_right _ (Finset.mem_union_left _ h)))
  · exact fresh_of_not_mem_support (fun h => freshParameters_fresh _ x
      (Finset.mem_union_right _ (Finset.mem_union_right _ h)))

end Instantiation

namespace WithoutInstantiation.ProofTree
open Instantiation

def instantiateComparisonPremise {Θ Ξ : Finset Formula} (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) (r : SubstRule) (hr : r.valid)
    (hr' : (mapRule σ ρ hs r).valid) (hf : RuleFresh r Θ Ξ)
    (ih : ∀ τ : Instantiation, ProofTree (τ.formulaSet Θ)
      (insert (τ.applyClass (ofExpr r.equation (SubstRule.equation_isFormula hr))) (τ.formulaSet Ξ))) :
    ProofTree (σ.formulaSet Θ)
      (insert (ofExpr (mapRule σ ρ hs r).equation (SubstRule.equation_isFormula hr')) (σ.formulaSet Ξ)) := by
  let es := r.comparisons.map (fun c => c.1.pointwiseEq c.2)
  have hes : ∀ e ∈ es, isFormula e := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    exact SubstPair.pointwiseEq_isFormula (hr.2.2.1 c hc)
  let fs := (mapRule σ ρ hs r).comparisons.map (fun c => c.1.pointwiseEq c.2)
  have hfs : ∀ e ∈ fs, isFormula e := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    exact SubstPair.pointwiseEq_isFormula (hr'.2.2.1 c hc)
  apply conjunction_intro fs hfs
  intro e he
  have hm : ∃ c ∈ r.comparisons, (mapPair σ c.1).pointwiseEq (c.2.map ρ) = e := by
    simpa only [fs, mapRule, List.map_map, Function.comp_def, List.mem_map] using he
  let c := Classical.choose hm
  have hc := (Classical.choose_spec hm).1
  have hec := (Classical.choose_spec hm).2
  let τ := σ.renameParameters ρ hs c.2
  have htΘ := formulaSet_renameParameters σ ρ hs c.2 Θ (fun x hx => (hf c hc x hx).1)
  have htΞ := formulaSet_renameParameters σ ρ hs c.2 Ξ (fun x hx => (hf c hc x hx).2)
  have hp := SubstPair.pointwiseEq_isFormula (hr.2.2.1 c hc)
  have htes : ∀ e ∈ es.map τ.apply, isFormula e := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact τ.hasSort (hes q hq)
  have hpMem : τ.apply (c.1.pointwiseEq c.2) ∈ es.map τ.apply :=
    List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩
  have de : ProofTree (σ.formulaSet Θ)
      (insert (ofExpr (foldFormulas Expr.and top (es.map τ.apply)) (conjunction_sorted _ htes))
        (σ.formulaSet Ξ)) := by
    simpa only [τ, htΘ, htΞ, applyClass_ofExpr, SubstRule.equation,
      apply_conjunction] using ih τ
  have dp := consequence de (conjunction_project _ htes _ hpMem)
  have heq : ofExpr (τ.apply (c.1.pointwiseEq c.2)) (τ.hasSort hp) = ofExpr e (hfs e he) := by
    apply (ofExpr_eq _ _).mpr
    rw [← hec]
    exact mapPair_pointwise σ ρ hs c.1 c.2 (hr.2.2.1 c hc)
  simpa only [heq] using dp

/-- The instantiated replacement rule, with the facts needed to apply either
its left or right form. All parameter freshening is confined to its construction. -/
structure InstantiatedReplacement (σ : Instantiation) (r : SubstRule) (hr : r.valid)
    (Θ Ξ : Finset Formula) where
  rule : SubstRule
  valid : rule.valid
  fresh : RuleFresh rule (σ.formulaSet Θ) (σ.formulaSet Ξ)
  source_eq : ofExpr rule.source valid.2.2.2.1 = σ.applyClass (ofExpr r.source hr.2.2.2.1)
  target_eq : ofExpr rule.target valid.2.2.2.2 = σ.applyClass (ofExpr r.target hr.2.2.2.2)
  comparison : ProofTree (σ.formulaSet Θ)
    (insert (ofExpr rule.equation (SubstRule.equation_isFormula valid)) (σ.formulaSet Ξ))

/-- Instantiate a replacement rule and rebuild its comparison premise, choosing
fresh parameters so that the residual assumptions remain unchanged. -/
def instantiateReplacement {Θ Ξ : Finset Formula} (σ : Instantiation) (r : SubstRule)
    (hr : r.valid) (hf : RuleFresh r Θ Ξ)
    (ih : ∀ τ : Instantiation, ProofTree (τ.formulaSet Θ)
      (insert (τ.applyClass (ofExpr r.equation (SubstRule.equation_isFormula hr))) (τ.formulaSet Ξ))) :
    InstantiatedReplacement σ r hr Θ Ξ := by
  let avoid := replacementForbiddenNames σ r Θ Ξ
  let ρ := freshParameters avoid
  have hs := freshParameters_sort avoid
  have hinj := freshParameters_injective avoid
  have hctx := fun x (_ : x ∈ r.context.params) => replacementForbiddenNames_context σ r Θ Ξ x
  have hcmp := fun c (hc : c ∈ r.comparisons) x (_ : x ∈ c.2) => replacementForbiddenNames_comparison σ r Θ Ξ c hc x
  have hv := mapRule_valid σ ρ hinj hs r hr hctx hcmp
  have hf' : RuleFresh (mapRule σ ρ hs r) (σ.formulaSet Θ) (σ.formulaSet Ξ) := by
    intro c hc x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact replacementForbiddenNames_fresh σ r Θ Ξ y
  have hsource : ofExpr (mapRule σ ρ hs r).source hv.2.2.2.1 =
      σ.applyClass (ofExpr r.source hr.2.2.2.1) := by
    rw [applyClass_ofExpr]; exact (ofExpr_eq _ _).mpr (.alpha (mapRule_source σ ρ hinj hs r hr hctx))
  have htarget : ofExpr (mapRule σ ρ hs r).target hv.2.2.2.2 =
      σ.applyClass (ofExpr r.target hr.2.2.2.2) := by
    rw [applyClass_ofExpr]; exact (ofExpr_eq _ _).mpr (.alpha (mapRule_target σ ρ hinj hs r hr hctx))
  have de := instantiateComparisonPremise σ ρ hs r hr hv hf ih
  exact ⟨mapRule σ ρ hs r, hv, hf', hsource, htarget, de⟩

end WithoutInstantiation.ProofTree
end Lisa.LambdaFol
