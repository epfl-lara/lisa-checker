import Lisa.SCLambdaToPure.AToPure.Readback
import Lisa.SCLambdaToPure.Pure
import Lisa.SCLambdaToPure.AToPure.PureProofs
import Lisa.SCLambdaToPure.AToPure.Reverse.Derivation
import Lisa.SCLambdaToPure.AToPure.Reverse.Equivalence
import Lisa.SCLambdaToPure.AToPure.Reverse.Embedding
import Lisa.SCLambdaToPure.Statements
namespace Lisa.SCLambdaToPure.Pure.ProofTree
open FirstOrder
variable {L : Language.{0, 0}} [DecidableEq (Formula L)] {Γ Δ : Context L}

/-- Conjunction commutativity, proved from sequent rules. -/
def and_comm (p q : Formula L) :
    ProofTree Γ (insert (.iff (.and p q) (.and q p)) Δ) := by
  apply equivalent
  · apply leftAnd
    have hq : ProofTree (insert p (insert q Γ)) (insert q Δ) :=
      hypothesisIn q (by simp) (by simp)
    have hp : ProofTree (insert p (insert q Γ)) (insert p Δ) :=
      hypothesisIn p (by simp) (by simp)
    simpa using ProofTree.rightAnd q p hq hp
  · apply leftAnd
    have hp : ProofTree (insert q (insert p Γ)) (insert p Δ) :=
      hypothesisIn p (by simp) (by simp)
    have hq : ProofTree (insert q (insert p Γ)) (insert q Δ) :=
      hypothesisIn q (by simp) (by simp)
    simpa using ProofTree.rightAnd p q hp hq

/-- First-order epsilon can preserve a logical equivalence underneath its binder. -/
def epsilon_and_comm (x : Identifier) (p q : Formula L)
    (hΓ : Fresh x Γ) (hΔ : Fresh x Δ) :
    ProofTree Γ (insert (.equal (epsilon_ x (.and p q))
      (epsilon_ x (.and q p))) Δ) :=
  epsilonExt x _ _ (and_comm p q) hΓ hΔ

end Lisa.SCLambdaToPure.Pure.ProofTree

namespace Tests.PureEpsilon
open Lisa Lisa.SCLambdaToPure
private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def y : SVar := ⟨⟨"y", 0⟩, ind⟩
private def p : Expr := .const (.named "P" (ind >> prop))

-- Epsilon's body is preserved, including a quantifier and both bound levels.
#guard match Readback.readTerm
    (Expr.epsilon_ (.lam x (Expr.forall_ y (Expr.eq (.var x) (.var y))))) with
  | some (.epsilon (.all (.equal (.var (.inr i)) (.var (.inr j))))) =>
      i.val == 0 && j.val == 1
  | _ => false

-- Epsilon can occur inside a quantified formula and refer to its outer binder.
#guard match Readback.readFormula
    (Expr.forall_ x (Expr.eq (Expr.epsilon_ (.lam y (Expr.eq (.var y) (.var x)))) (.var x))) with
  | some (.all (.equal (.epsilon (.equal (.var (.inr i)) (.var (.inr j)))) (.var (.inr k)))) =>
      i.val == 1 && j.val == 0 && k.val == 0
  | _ => false

-- A higher-order redex normalizes before epsilon readback.
private def redex : Expr :=
  .app (.lam ⟨⟨"F", 0⟩, ind >> prop⟩
    (Expr.epsilon_ (.var ⟨⟨"F", 0⟩, ind >> prop⟩))) p
#guard match Readback.readTerm redex with
  | some (.epsilon (.rel c ts)) =>
      c.id == (⟨"P", 0⟩ : Identifier) && (List.ofFn ts).length == 1
  | _ => false

-- Shadowing does not capture an unrelated free variable inside nested epsilon.
#guard match Readback.readTerm
    (Expr.epsilon_ (.lam x (Expr.eq (.var x)
      (Expr.epsilon_ (.lam x (Expr.eq (.var x) (.var y))))))) with
  | some (.epsilon (.equal (.var (.inr i))
      (.epsilon (.equal (.var (.inr j)) (.var (.inl k)))))) =>
      i.val == 0 && j.val == 1 && k == y.id
  | _ => false

-- Unsupported higher-order free symbols still fail instead of becoming opaque atoms.
#guard (Readback.readFormula
    (.app (.var ⟨⟨"H", 0⟩, (ind >> prop) >> prop⟩) p)).isNone

open Pure
abbrev L := Readback.language
local instance (n : Nat) : OfNat Identifier n := ⟨⟨"v", n⟩⟩
private def v (i : Identifier) : Pure.Term L := .var (.inl i)
private def body : Pure.Formula L := .equal (v 0) (v 1)

-- The inserted free 0 remains free under epsilon binding the original free 0.
example : (epsilon_ 0 body).subst (single 1 (v 0)) =
    (.epsilon (.equal (.var (.inr 0)) (.var (.inl 0))) :
      Pure.Term L) := rfl

-- Simultaneous replacement does not apply one replacement to another's image.
private def swapVars : Substitution L Identifier 0 Identifier 0 :=
  fun z => match z with
    | .inl n => if n = 0 then v 1 else if n = 1 then v 0 else v n
    | .inr i => Fin.elim0 i
example : body.subst swapVars = .equal (v 1) (v 0) := rfl

noncomputable section
local instance : DecidableEq (Pure.Formula L) := Classical.decEq _

-- A genuine witness premise produces an epsilon witness.
example : Nonempty (ProofTree (L := L)
    {.equal (v 1) (v 1)}
    {substOne 0 (epsilon_ 0 body) body}) := by
  classical
  exact ⟨ProofTree.epsilonWitness (Γ := {.equal (v 1) (v 1)}) (Δ := ∅) 0 body (v 1)
    (by simpa [body, substOne, single, BFormula.subst, BTerm.subst, v] using
      (ProofTree.hypothesis (.equal (v 1) (v 1))))⟩

-- Congruence underneath epsilon, with nonempty residual contexts.
example : Nonempty (ProofTree (L := L)
    {.top} (insert (.equal (epsilon_ 0 (.and body .top))
      (epsilon_ 0 (.and .top body))) {.bot})) := by
  classical
  exact ⟨ProofTree.epsilon_and_comm 0 body .top
    (by simp [Fresh, BFormula.freeVars]) (by simp [Fresh, BFormula.freeVars])⟩

#print axioms OrderedDerivation.epsilonExt
#print axioms FirstOrderShape.canonical_lamfol
#print axioms Readback.readFormula_isSome
#print axioms Readback.formula_representation
#print axioms Readback.term_representation
#print axioms Readback.formula_provable_equivalence
#print axioms PureEmbedding.formula_substOne
#print axioms PureEmbedding.toOrdered
#print axioms Syntactic.substitution_rule_equiv_contexts
#print axioms Syntactic.ordered_toPure
#print axioms ordered_iff_pure
#print axioms a_iff_pure
#print axioms b_iff_pure
#print axioms B.toA
#print axioms A.toPure

-- The complete theorem retains the original assumptions and both succedents.
example {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    OrderedReduction.Provable Γ Δ ↔ Pure.Provable
      (Readback.canonicalContext Γ) (Readback.canonicalContext Δ) :=
  ordered_iff_pure hΓ hΔ hbΓ hbΔ

-- Reverse transport covers contextual epsilon extensionality, not just readback.
example : Nonempty (Ordered.AlphaBetaEtaProof
    (PureEmbedding.context {.top})
    (PureEmbedding.context 
      (insert (BFormula.equal (epsilon_ 0 (.and body .top))
        (epsilon_ 0 (.and .top body))) {.bot}))) := by
  exact ⟨PureEmbedding.toOrdered (ProofTree.epsilon_and_comm (Γ := {.top}) (Δ := {.bot}) 0 body .top
      (by simp [Fresh, BFormula.freeVars]) (by simp [Fresh, BFormula.freeVars]))⟩

end

-- Complete forward transport with simultaneous images that mention one
-- another's parameters. Sequential replacement would produce a different body.
private def simultaneous : SubstRule :=
  ⟨[(⟨.var x, .var y⟩, []), (⟨.var y, .var x⟩, [])], ⟨[x, y], Expr.eq (.var x) (.var y)⟩⟩

private theorem simultaneous_valid : simultaneous.valid := by decide

private noncomputable def simultaneousProof : Ordered.AlphaBetaEtaProof
    ({simultaneous.source} ∪ {simultaneous.equation}) {simultaneous.target} := by
  have hs : isFormula simultaneous.source := simultaneous_valid.2.2.2.1
  have he := SubstRule.equation_isFormula simultaneous_valid
  simpa using Ordered.ProofTree.rightSubst (Γ := {simultaneous.source}) (Δ := ∅)
    (Θ := {simultaneous.equation}) (Ξ := ∅) simultaneous
    (Orthologic.Derivation.singleton_sorted hs) isFSet_empty
    (Orthologic.Derivation.singleton_sorted he) isFSet_empty simultaneous_valid
    (by decide) (.hypothesis _ hs) (.hypothesis _ he)

example : Pure.Provable
    (Readback.canonicalContext ({simultaneous.source} ∪ {simultaneous.equation}))
    (Readback.canonicalContext {simultaneous.target}) := by
  apply OrderedReduction.toPure
    (by unfold isFSet isFormula Expr.hasSort; decide)
    (by unfold isFSet isFormula Expr.hasSort; decide)
    (by
      simp only [Finset.mem_union, Finset.mem_singleton, forall_eq_or_imp]
      constructor
      · change FirstOrderBoundary (Expr.eq (.var x) (.var y))
        refine ⟨⟨⟨.eq, trivial⟩, trivial⟩, ?_⟩
        simp [Expr.eq, Expr.freeVars, x, y]
      · intro a ha
        subst a
        change FirstOrderBoundary (Expr.and (Expr.eq (.var x) (.var y)) (Expr.eq (.var y) (.var x)))
        refine ⟨⟨⟨.and, ⟨⟨.eq, trivial⟩, trivial⟩⟩, ⟨⟨.eq, trivial⟩, trivial⟩⟩, ?_⟩
        simp [Expr.and, Expr.eq, Expr.freeVars, x, y])
    (by
      simp only [Finset.mem_singleton, forall_eq]
      change FirstOrderBoundary (Expr.eq (.var y) (.var x))
      refine ⟨⟨⟨.eq, trivial⟩, trivial⟩, ?_⟩
      simp [Expr.eq, Expr.freeVars, x, y])
  exact ⟨simultaneousProof⟩

-- An intermediate cut may contain a schematic symbol of higher-order sort,
-- although the final sequent contains no such symbol.
private def higher : Expr := .app (.var ⟨⟨"H", 0⟩, (ind >> prop) >> prop⟩) (.lam x Expr.top)
private theorem higher_sorted : isFormula higher := rfl
private noncomputable def higherCut : Ordered.AlphaBetaEtaProof ∅ {Expr.top} := by
  have first : Ordered.AlphaBetaEtaProof ∅ (insert higher {Expr.top}) :=
    Ordered.ProofTree.weakening isFSet_empty (by unfold isFSet isFormula Expr.hasSort; decide)
      isFSet_empty (by unfold isFSet isFormula Expr.hasSort; decide)
      .rightTrue (by simp) (by simp)
  have second : Ordered.AlphaBetaEtaProof {higher} {Expr.top} :=
    Ordered.ProofTree.weakening isFSet_empty (by unfold isFSet isFormula Expr.hasSort; decide)
      (by unfold isFSet isFormula Expr.hasSort; decide) (by unfold isFSet isFormula Expr.hasSort; decide)
      .rightTrue (by simp) (by simp)
  simpa using Ordered.ProofTree.cut (Γ := ∅) (Δ := {Expr.top}) (Ω := ∅) (Ξ := {Expr.top}) higher
    isFSet_empty (by unfold isFSet isFormula Expr.hasSort; decide)
    isFSet_empty (by unfold isFSet isFormula Expr.hasSort; decide) higher_sorted first second

example : Pure.Provable ∅ {Pure.BFormula.top (L := L)} := by
  have h := Syntactic.ordered_toPure higherCut isFSet_empty (by unfold isFSet isFormula Expr.hasSort; decide) _ Syntactic.Assignment.grounding_fixesConstants
  simpa only [Syntactic.Assignment.context_empty, Syntactic.Assignment.context_singleton,
    Syntactic.Assignment.formula_top Syntactic.Assignment.grounding_fixesConstants] using h

-- Schematic instantiation can introduce epsilon. Its instantiation node is
-- eliminated in B → A before normalization and readback into Pure.
private def schema : Subst := (∅ : Subst).insert x (Expr.epsilon_ (.lam y (Expr.eq (.var y) (.var y))))
private theorem schema_sorted : Subst.wellSorted schema := by
  apply Subst.wellSorted_insert
  · unfold Subst.wellSorted
    decide
  · rfl
private noncomputable def schemaProof : Ordered.AlphaBetaEtaProof ∅
    (({Expr.eq (.var x) (.var x)} : Finset Expr).image (Expr.subst schema)) := by
  simpa using Ordered.ProofTree.instSchema schema isFSet_empty
    (by unfold isFSet isFormula Expr.hasSort; decide) schema_sorted
    (Ordered.ProofTree.rightRefl (.var x) rfl)

example : Pure.Provable ∅
    (Syntactic.Assignment.grounding.context (({Expr.eq (.var x) (.var x)} : Finset Expr).image (Expr.subst schema))) := by
  simpa only [Syntactic.Assignment.context_empty] using
    Syntactic.ordered_toPure schemaProof isFSet_empty (by unfold isFSet isFormula Expr.hasSort; decide) _ Syntactic.Assignment.grounding_fixesConstants

end Tests.PureEpsilon

