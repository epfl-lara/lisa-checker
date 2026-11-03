import Lisa.LambdaFol
import Lean

namespace Tests.LambdaFol

open Lisa Lisa.LambdaFol

private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def y : SVar := ⟨⟨"y", 0⟩, ind⟩
private def p : Expr := .const (.named "P" prop)
private def f : Expr := .const (.named "f" (ind >> ind))
private def c : Expr := .const (.named "c" ind)
private def z : SVar := ⟨⟨"z", 0⟩, prop⟩

-- A beta redex and its reduct are the same WithoutInstantiation formula, without a conversion rule.
example : LambdaFol.ofExpr (.app (.lam z (.var z)) p) (by rfl) = LambdaFol.ofExpr p (by rfl) := by
  apply (LambdaFol.ofExpr_eq _ _).mpr
  simpa [Expr.substOne, Expr.subst, Subst.subst, z] using
    AlphaBetaEta.beta z (.var z) p (by rfl)

example : WithoutInstantiation.ProofTree
    {LambdaFol.ofExpr (.app (.lam z (.var z)) p) (by rfl)} {LambdaFol.ofExpr p (by rfl)} := by
  have he : LambdaFol.ofExpr (s := prop) (.app (.lam z (.var z)) p) (by rfl) = LambdaFol.ofExpr p (by rfl) := by
    apply (LambdaFol.ofExpr_eq _ _).mpr
    simpa [Expr.substOne, Expr.subst, Subst.subst, z] using
      AlphaBetaEta.beta z (.var z) p (by rfl)
  exact (congrArg (fun a => WithoutInstantiation.ProofTree {a} {LambdaFol.ofExpr p (by rfl)}) he).mpr (.hypothesis _)

-- Alpha-renaming is also formula identity.
example : LambdaFol.ofExpr (Expr.forall_ x (Expr.eq (.var x) (.var x))) (by rfl) =
    LambdaFol.ofExpr (Expr.forall_ y (Expr.eq (.var y) (.var y))) (by rfl) := by
  exact (LambdaFol.ofExpr_eq _ _).mpr (.alpha (by decide))

-- Quantifier introduction uses freshness of the residual contexts.
example : WithoutInstantiation.ProofTree ∅
    {LambdaFol.ofExpr (Expr.forall_ x (Expr.eq (.var x) (.var x))) (by rfl)} := by
  exact .rightForall (Γ := ∅) (Δ := ∅) x (Expr.eq (.var x) (.var x)) rfl (by rfl)
    (.refl (.var x) (by rfl))
    (by simp [LambdaFol.Fresh]) (by simp [LambdaFol.Fresh])

-- Freshness can use a beta-reduced representative that drops an unused variable.
example : LambdaFol.Fresh x {LambdaFol.ofExpr (.app (.lam z p) (Expr.eq (.var x) (.var x))) (by rfl)} := by
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  refine ⟨p, by rfl, ?_, by simp [p]⟩
  apply (LambdaFol.ofExpr_eq _ _).mpr
  simpa [Expr.substOne, Expr.subst, Subst.subst, p] using
    (AlphaBetaEta.beta z p (Expr.eq (.var x) (.var x)) (by rfl)).symm

-- Schematic instantiation may introduce the original eigenvariable freely.
-- The conclusion must bind a fresh variable instead of capturing that occurrence.
private def rx : Expr := .app (.const (.named "R" (ind >> prop))) (.var x)
private def collision : Instantiation := ⟨.cons z rx .nil, ⟨rfl, trivial⟩⟩

private noncomputable def vacuousAll : WithoutInstantiation.ProofTree {LambdaFol.ofExpr (.var z) (by rfl)}
    {LambdaFol.ofExpr (Expr.forall_ x (.var z)) (by rfl)} := by
  apply WithoutInstantiation.ProofTree.rightForall (Γ := {LambdaFol.ofExpr (.var z) (by rfl)}) (Δ := ∅)
    x (.var z) rfl (by rfl)
  · exact .hypothesis _
  · intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact ⟨.var z, rfl, rfl, by decide⟩
  · intro q hq; simp at hq

private noncomputable def instantiatedAll : LambdaFol.ProofTree
    {LambdaFol.ofExpr rx (by rfl)} {LambdaFol.ofExpr (Expr.forall_ y rx) (by rfl)} := by
  have h := LambdaFol.ProofTree.instSchema collision (LambdaFol.ProofTree.ofWithoutInstantiation vacuousAll)
  simp only [Instantiation.formulaSet_singleton] at h
  rw [collision.applyClass_forall x y rfl (.var z) rfl rfl (by decide),
    Instantiation.applyClass_ofExpr] at h
  exact h

example : WithoutInstantiation.Provable {LambdaFol.ofExpr rx (by rfl)}
    {LambdaFol.ofExpr (Expr.forall_ y rx) (by rfl)} := ⟨LambdaFol.ProofTree.toWithoutInstantiation instantiatedAll⟩

-- The instantiation can occur below a subsequent ordinary inference.
example : WithoutInstantiation.Provable
    {LambdaFol.ofExpr (Expr.neg (Expr.forall_ y rx)) (by rfl), LambdaFol.ofExpr rx (by rfl)} ∅ := by
  refine ⟨LambdaFol.ProofTree.toWithoutInstantiation ?_⟩
  exact LambdaFol.ProofTree.leftNot (Expr.forall_ y rx) (by rfl) instantiatedAll

-- Variables of function sort are instantiated by lambda expressions. Conversion
-- of the resulting beta redex is equality in the quotient, without another rule.
private def higherVar : SVar := ⟨⟨"H", 0⟩, prop >> prop⟩
private def higherSubst : Instantiation :=
  ⟨.cons higherVar (.lam z (.var z)) .nil, ⟨rfl, trivial⟩⟩

private theorem higherInstance :
    higherSubst.applyClass (LambdaFol.ofExpr (.app (.var higherVar) p) (by rfl)) =
      LambdaFol.ofExpr p (by rfl) := by
  rw [Instantiation.applyClass_ofExpr]
  apply (LambdaFol.ofExpr_eq _ _).mpr
  simpa [Expr.substOne, Expr.subst, Subst.subst, p] using AlphaBetaEta.beta z (.var z) p (by rfl)

private noncomputable def higherInstProof : LambdaFol.ProofTree
    {LambdaFol.ofExpr p (by rfl)} {LambdaFol.ofExpr p (by rfl)} := by
  have h := LambdaFol.ProofTree.instSchema higherSubst
    (LambdaFol.ProofTree.hypothesis (LambdaFol.ofExpr (.app (.var higherVar) p) (by rfl)))
  simpa only [Instantiation.formulaSet_singleton, higherInstance] using h

-- End-to-end LambdaFol transport now uses the independent epsilon target.
example : PureFol.Provable
    {FirstOrderAssignment.defaultAssignment.toPureFolFormula p} {FirstOrderAssignment.defaultAssignment.toPureFolFormula p} := by
  simpa using LambdaFol.ProofTree.provable_toPureFol higherInstProof _ FirstOrderAssignment.defaultAssignment_fixesConstants

-- Simultaneous replacement keeps the free variable in an image intact; a second
-- entry is not recursively applied to the first entry's image.
private def simultaneous : Instantiation :=
  ⟨.cons x (.var y) (.cons y c .nil), ⟨rfl, rfl, trivial⟩⟩

example : simultaneous.applyClass (LambdaFol.ofExpr (Expr.eq (.var x) (.var y)) (by rfl)) =
    LambdaFol.ofExpr (Expr.eq (.var y) c) (by rfl) := by
  rw [Instantiation.applyClass_ofExpr]
  rfl

-- The generalized rule is below an instantiation that introduces its old
-- pointwise parameter into a residual assumption. LambdaFol → WithoutInstantiation must freshen that
-- parameter, while retaining the assumption and the simultaneous replacement template.
private def k : SVar := ⟨⟨"k", 0⟩, prop >> prop⟩
private def hole : SVar := ⟨⟨"hole", 0⟩, prop >> prop⟩
private def arg : SVar := ⟨⟨"arg", 0⟩, prop⟩
private def pointwise : SubstRule :=
  ⟨[(⟨.var k, .var k⟩, [z])], ⟨[hole], .app (.var hole) (.var arg)⟩⟩
private theorem pointwise_valid : pointwise.valid := by decide

private noncomputable def comparisonProof : WithoutInstantiation.ProofTree {LambdaFol.ofExpr (.var arg) rfl}
    {LambdaFol.ofExpr pointwise.equation (SubstRule.equation_isFormula pointwise_valid)} := by
  let e : Expr := .app (.var k) (.var z)
  have he : isFormula e := rfl
  have impl : WithoutInstantiation.ProofTree ∅ {LambdaFol.ofExpr (Expr.imp e e) (isFormula_imp he he)} :=
    .rightImp (Γ := ∅) (Δ := ∅) e e he he (.hypothesis _)
  have eqv := WithoutInstantiation.ProofTree.rightIff e e he he (Δ := ∅) (Δ₁ := ∅) impl impl
  apply WithoutInstantiation.ProofTree.weakening (by simpa [pointwise, SubstRule.equation, SubstPair.pointwiseEq,
    SubstPair.sort, foldFormulas, Expr.applied, k, e] using eqv)
  · simp
  · rfl

private noncomputable def pointwiseProof : WithoutInstantiation.ProofTree
    ({LambdaFol.ofExpr pointwise.source pointwise_valid.2.2.2.1} ∪ {LambdaFol.ofExpr (.var arg) rfl})
    {LambdaFol.ofExpr pointwise.target pointwise_valid.2.2.2.2} := by
  apply WithoutInstantiation.ProofTree.rightReplace (Δ := ∅) (Ξ := ∅) pointwise pointwise_valid
    (fun pair hp v hv => by
      have hp' : pair = (⟨.var k, .var k⟩, [z]) := by simpa [pointwise] using hp
      subst pair
      have hv' : v = z := by simpa using hv
      subst v
      constructor
      · intro q hq
        obtain rfl := Finset.mem_singleton.mp hq
        exact ⟨.var arg, rfl, rfl, by decide⟩
      · intro q hq; simp at hq)
    (.hypothesis _) comparisonProof

private def parameterCollision : Instantiation := ⟨.cons arg (.var z) .nil, ⟨rfl, trivial⟩⟩

example : WithoutInstantiation.Provable
    (parameterCollision.formulaSet
      ({LambdaFol.ofExpr pointwise.source pointwise_valid.2.2.2.1} ∪ {LambdaFol.ofExpr (.var arg) rfl}))
    (parameterCollision.formulaSet {LambdaFol.ofExpr pointwise.target pointwise_valid.2.2.2.2}) :=
  ⟨LambdaFol.ProofTree.toWithoutInstantiation (.instSchema parameterCollision (LambdaFol.ProofTree.ofWithoutInstantiation pointwiseProof))⟩

-- An instantiation above an epsilon witness rule is also removed, even if its
-- image contains the old binder name freely.
private def epsilonBody : Expr := Expr.and (.var z) (Expr.eq (.var x) (.var x))
private noncomputable def epsilonProof : WithoutInstantiation.ProofTree
    {LambdaFol.ofExpr (Expr.substOne x c epsilonBody) (isFormula_substOne rfl rfl rfl)}
    {LambdaFol.ofExpr (Expr.substOne x (Expr.epsilon_ (.lam x epsilonBody)) epsilonBody)
      (isFormula_substOne rfl (isTerm_epsilon rfl rfl) rfl)} :=
  .rightEpsilon (Δ := ∅) x epsilonBody c rfl rfl rfl (.hypothesis _)

example : WithoutInstantiation.Provable
    (collision.formulaSet {LambdaFol.ofExpr (Expr.substOne x c epsilonBody) (isFormula_substOne rfl rfl rfl)})
    (collision.formulaSet {LambdaFol.ofExpr (Expr.substOne x (Expr.epsilon_ (.lam x epsilonBody)) epsilonBody)
      (isFormula_substOne rfl (isTerm_epsilon rfl rfl) rfl)}) :=
  ⟨LambdaFol.ProofTree.toWithoutInstantiation (.instSchema collision (LambdaFol.ProofTree.ofWithoutInstantiation epsilonProof))⟩

-- The public intermediate results use exactly the same PureFol boundary as Ordered.
example {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p) :
    WithoutInstantiation.Provable (LambdaFol.formulaSet Γ hΓ) (LambdaFol.formulaSet Δ hΔ) ↔
      PureFol.Provable (PureFolTranslation.canonicalFormulaSet Γ) (PureFolTranslation.canonicalFormulaSet Δ) :=
  withoutInstantiation_iff_pureFol hΓ hΔ hbΓ hbΔ

end Tests.LambdaFol

-- Guard the architecture as well as the theorem statement: the final proof
-- must actually pass through LambdaFol → WithoutInstantiation and WithoutInstantiation → PureFol, without a semantic shortcut.
-- Inspect the forward proof alone: the reverse direction also uses LambdaFol → WithoutInstantiation.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let (_, deps) := ((CollectAxioms.collect ``Lisa.LambdaFol.OrderedAlphaBetaEta.toPureFol).run env).run {}
  for n in [``Lisa.LambdaFol.ProofTree.ofOrdered, ``Lisa.LambdaFol.ProofTree.toWithoutInstantiation,
      ``Lisa.LambdaFol.WithoutInstantiation.ProofTree.instantiate, ``Lisa.LambdaFol.WithoutInstantiation.ProofTree.provable_toPureFol] do
    unless deps.visited.contains n do
      throwError "The final reduction bypasses required stage {n}"
  for n in deps.visited do
    if let some i := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[i]!
      if "Lisa.LambdaFol.Reference.".isPrefixOf m.toString then
        throwError "The syntactic reduction depends on reference semantics: {n}"

-- Reject proof placeholders or additional assumptions, not merely semantic imports.
open Lean Elab Command in
run_elab do
  for root in [``Lisa.LambdaFol.ordered_iff_pureFol, ``Lisa.LambdaFol.withoutInstantiation_iff_pureFol,
      ``Lisa.LambdaFol.ordered_iff_withoutInstantiation,
      ``Lisa.LambdaFol.lambdaFol_iff_pureFol, ``Lisa.LambdaFol.lambdaFol_iff_withoutInstantiation,
      ``Lisa.LambdaFol.PureFolTranslation.fromExprFormula_roundtrip] do
    for axiomName in ← collectAxioms root do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {root}"
