import Lisa.SCLambdaToPure.OrderedToA.SubstitutionRule
import Lisa.SCLambdaToPure.OrderedToA.Conjunction
/-! The generalized replacement rule survives schematic instantiation.
Each comparison is first projected from its premise with its own fresh parameter
renaming; the resulting comparisons are then conjoined again. -/
noncomputable section
namespace Lisa.SCLambdaToPure
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
def ruleAvoid (σ : Instantiation) (r : SubstRule) (Θ Ξ : A.Context) : Finset SVar := by
  classical
  exact (σ.substitution.rangeFreeVars ∪ r.context.body.freeVars) ∪
    r.comparisons.toFinset.biUnion (fun c => (σ.apply c.1.source).freeVars ∪ (σ.apply c.1.target).freeVars) ∪
    (support (σ.context Θ) ∪ support (σ.context Ξ))

theorem ruleAvoid_context (σ : Instantiation) (r : SubstRule) (Θ Ξ : A.Context) (x : SVar) :
    freshParameters (ruleAvoid σ r Θ Ξ) x ∉ σ.substitution.rangeFreeVars ∪ r.context.body.freeVars := by
  intro h
  exact freshParameters_fresh _ x (Finset.mem_union_left _ (Finset.mem_union_left _ h))

theorem ruleAvoid_comparison (σ : Instantiation) (r : SubstRule) (Θ Ξ : A.Context)
    (c : SubstPair × List SVar) (hc : c ∈ r.comparisons) (x : SVar) :
    freshParameters (ruleAvoid σ r Θ Ξ) x ∉ (σ.apply c.1.source).freeVars ∪ (σ.apply c.1.target).freeVars := by
  intro h
  exact freshParameters_fresh _ x (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, by simpa using hc, h⟩)))

theorem ruleAvoid_fresh (σ : Instantiation) (r : SubstRule) (Θ Ξ : A.Context) (x : SVar) :
    A.Fresh (freshParameters (ruleAvoid σ r Θ Ξ) x) (σ.context Θ) ∧
    A.Fresh (freshParameters (ruleAvoid σ r Θ Ξ) x) (σ.context Ξ) := by
  constructor
  · exact fresh_of_not_mem_support (fun h => freshParameters_fresh _ x
      (Finset.mem_union_right _ (Finset.mem_union_left _ h)))
  · exact fresh_of_not_mem_support (fun h => freshParameters_fresh _ x
      (Finset.mem_union_right _ (Finset.mem_union_right _ h)))

end Instantiation

namespace A.ProofTree
open Instantiation

def instantiateEquation {Θ Ξ : Context} (σ : Instantiation) (ρ : SVar → SVar)
    (hs : ∀ x, (ρ x).sort = x.sort) (r : SubstRule) (hr : r.valid)
    (hr' : (mapRule σ ρ hs r).valid) (hf : RuleFresh r Θ Ξ)
    (ih : ∀ τ : Instantiation, ProofTree (τ.context Θ)
      (insert (τ.expression (ofExpr r.equation (SubstRule.equation_isFormula hr))) (τ.context Ξ))) :
    ProofTree (σ.context Θ)
      (insert (ofExpr (mapRule σ ρ hs r).equation (SubstRule.equation_isFormula hr')) (σ.context Ξ)) := by
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
  have htΘ := context_renameParameters σ ρ hs c.2 Θ (fun x hx => (hf c hc x hx).1)
  have htΞ := context_renameParameters σ ρ hs c.2 Ξ (fun x hx => (hf c hc x hx).2)
  have hp := SubstPair.pointwiseEq_isFormula (hr.2.2.1 c hc)
  have htes : ∀ e ∈ es.map τ.apply, isFormula e := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact τ.hasSort (hes q hq)
  have hpMem : τ.apply (c.1.pointwiseEq c.2) ∈ es.map τ.apply :=
    List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩
  have de : ProofTree (σ.context Θ)
      (insert (ofExpr (foldFormulas Expr.and top (es.map τ.apply)) (conjunction_sorted _ htes))
        (σ.context Ξ)) := by
    simpa only [τ, htΘ, htΞ, expression_ofExpr, SubstRule.equation,
      apply_conjunction] using ih τ
  have dp := consequence de (conjunction_project _ htes _ hpMem)
  have heq : ofExpr (τ.apply (c.1.pointwiseEq c.2)) (τ.hasSort hp) = ofExpr e (hfs e he) := by
    apply (ofExpr_eq _ _).mpr
    rw [← hec]
    exact mapPair_pointwise σ ρ hs c.1 c.2 (hr.2.2.1 c hc)
  simpa only [heq] using dp

end A.ProofTree
end Lisa.SCLambdaToPure
