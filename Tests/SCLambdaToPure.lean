import Lisa.SCLambdaToPure
import Lean

namespace Tests.SCLambdaToPure

open Lisa Lisa.SCLambdaToPure

private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def y : SVar := ⟨⟨"y", 0⟩, ind⟩
private def p : Expr := .const (.named "P" prop)
private def f : Expr := .const (.named "f" (ind >> ind))
private def c : Expr := .const (.named "c" ind)
private def z : SVar := ⟨⟨"z", 0⟩, prop⟩

-- A beta redex and its reduct are the same A formula, without a conversion rule.
example : A.ofExpr (.app (.lam z (.var z)) p) (by rfl) = A.ofExpr p (by rfl) := by
  apply (A.ofExpr_eq _ _).mpr
  simpa [Expr.substOne, Expr.subst, Subst.subst, z] using
    AlphaBetaEta.beta z (.var z) p (by rfl)

example : A.ProofTree
    {A.ofExpr (.app (.lam z (.var z)) p) (by rfl)} {A.ofExpr p (by rfl)} := by
  have he : A.ofExpr (s := prop) (.app (.lam z (.var z)) p) (by rfl) = A.ofExpr p (by rfl) := by
    apply (A.ofExpr_eq _ _).mpr
    simpa [Expr.substOne, Expr.subst, Subst.subst, z] using
      AlphaBetaEta.beta z (.var z) p (by rfl)
  exact (congrArg (fun a => A.ProofTree {a} {A.ofExpr p (by rfl)}) he).mpr (.hypothesis _)

-- Alpha-renaming is also formula identity.
example : A.ofExpr (Expr.forall_ x (Expr.eq (.var x) (.var x))) (by rfl) =
    A.ofExpr (Expr.forall_ y (Expr.eq (.var y) (.var y))) (by rfl) := by
  exact (A.ofExpr_eq _ _).mpr (.alpha (by decide))

-- Quantifier introduction uses freshness of the residual contexts.
example : A.ProofTree ∅
    {A.ofExpr (Expr.forall_ x (Expr.eq (.var x) (.var x))) (by rfl)} := by
  exact .rightForall (Γ := ∅) (Δ := ∅) x (Expr.eq (.var x) (.var x)) rfl (by rfl)
    (.refl (.var x) (by rfl))
    (by simp [A.Fresh]) (by simp [A.Fresh])

-- Freshness can use a beta-reduced representative that drops an unused variable.
example : A.Fresh x {A.ofExpr (.app (.lam z p) (Expr.eq (.var x) (.var x))) (by rfl)} := by
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  refine ⟨p, by rfl, ?_, by simp [p]⟩
  apply (A.ofExpr_eq _ _).mpr
  simpa [Expr.substOne, Expr.subst, Subst.subst, p] using
    (AlphaBetaEta.beta z p (Expr.eq (.var x) (.var x)) (by rfl)).symm

-- Schematic instantiation may introduce the original eigenvariable freely.
-- The conclusion must bind a fresh variable instead of capturing that occurrence.
private def rx : Expr := .app (.const (.named "R" (ind >> prop))) (.var x)
private def collision : Instantiation := ⟨.cons z rx .nil, ⟨rfl, trivial⟩⟩

private noncomputable def vacuousAll : A.ProofTree {A.ofExpr (.var z) (by rfl)}
    {A.ofExpr (Expr.forall_ x (.var z)) (by rfl)} := by
  apply A.ProofTree.rightForall (Γ := {A.ofExpr (.var z) (by rfl)}) (Δ := ∅)
    x (.var z) rfl (by rfl)
  · exact .hypothesis _
  · intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact ⟨.var z, rfl, rfl, by decide⟩
  · intro q hq; simp at hq

private noncomputable def instantiatedAll : B.ProofTree
    {A.ofExpr rx (by rfl)} {A.ofExpr (Expr.forall_ y rx) (by rfl)} := by
  have h := B.ProofTree.instSchema collision (B.ofA vacuousAll)
  simp only [Instantiation.context_singleton] at h
  rw [collision.expression_forall x y rfl (.var z) rfl rfl (by decide),
    Instantiation.expression_ofExpr] at h
  exact h

example : A.Provable {A.ofExpr rx (by rfl)}
    {A.ofExpr (Expr.forall_ y rx) (by rfl)} := ⟨B.toA instantiatedAll⟩

-- The instantiation can occur below a subsequent ordinary inference.
example : A.Provable
    {A.ofExpr (Expr.neg (Expr.forall_ y rx)) (by rfl), A.ofExpr rx (by rfl)} ∅ := by
  refine ⟨B.toA ?_⟩
  exact B.ProofTree.leftNot (Expr.forall_ y rx) (by rfl) instantiatedAll

-- Variables of function sort are instantiated by lambda expressions. Conversion
-- of the resulting beta redex is equality in the quotient, without another rule.
private def higherVar : SVar := ⟨⟨"H", 0⟩, prop >> prop⟩
private def higherSubst : Instantiation :=
  ⟨.cons higherVar (.lam z (.var z)) .nil, ⟨rfl, trivial⟩⟩

private theorem higherInstance :
    higherSubst.expression (A.ofExpr (.app (.var higherVar) p) (by rfl)) =
      A.ofExpr p (by rfl) := by
  rw [Instantiation.expression_ofExpr]
  apply (A.ofExpr_eq _ _).mpr
  simpa [Expr.substOne, Expr.subst, Subst.subst, p] using AlphaBetaEta.beta z (.var z) p (by rfl)

private noncomputable def higherInstProof : B.ProofTree
    {A.ofExpr p (by rfl)} {A.ofExpr p (by rfl)} := by
  have h := B.ProofTree.instSchema higherSubst
    (B.ProofTree.hypothesis (A.ofExpr (.app (.var higherVar) p) (by rfl)))
  simpa only [Instantiation.context_singleton, higherInstance] using h

-- End-to-end B transport now uses the independent epsilon target.
example : Pure.Provable
    {Syntactic.Assignment.grounding.formula p} {Syntactic.Assignment.grounding.formula p} := by
  simpa using B.toPure higherInstProof _ Syntactic.Assignment.grounding_fixesConstants

-- Simultaneous replacement keeps the free variable in an image intact; a second
-- entry is not recursively applied to the first entry's image.
private def simultaneous : Instantiation :=
  ⟨.cons x (.var y) (.cons y c .nil), ⟨rfl, rfl, trivial⟩⟩

example : simultaneous.expression (A.ofExpr (Expr.eq (.var x) (.var y)) (by rfl)) =
    A.ofExpr (Expr.eq (.var y) c) (by rfl) := by
  rw [Instantiation.expression_ofExpr]
  rfl

-- The generalized rule is below an instantiation that introduces its old
-- pointwise parameter into a residual assumption. B → A must freshen that
-- parameter, while retaining the assumption and the simultaneous context.
private def k : SVar := ⟨⟨"k", 0⟩, prop >> prop⟩
private def hole : SVar := ⟨⟨"hole", 0⟩, prop >> prop⟩
private def arg : SVar := ⟨⟨"arg", 0⟩, prop⟩
private def pointwise : SubstRule :=
  ⟨[(⟨.var k, .var k⟩, [z])], ⟨[hole], .app (.var hole) (.var arg)⟩⟩
private theorem pointwise_valid : pointwise.valid := by decide

private noncomputable def comparisonProof : A.ProofTree {A.ofExpr (.var arg) rfl}
    {A.ofExpr pointwise.equation (SubstRule.equation_isFormula pointwise_valid)} := by
  let e : Expr := .app (.var k) (.var z)
  have he : isFormula e := rfl
  have impl : A.ProofTree ∅ {A.ofExpr (Expr.imp e e) (isFormula_imp he he)} :=
    .rightImp (Γ := ∅) (Δ := ∅) e e he he (.hypothesis _)
  have eqv := A.ProofTree.rightIff e e he he (Δ := ∅) (Δ₁ := ∅) impl impl
  apply A.ProofTree.weakening (by simpa [pointwise, SubstRule.equation, SubstPair.pointwiseEq,
    SubstPair.sort, foldFormulas, Expr.applied, k, e] using eqv)
  · simp
  · rfl

private noncomputable def pointwiseProof : A.ProofTree
    ({A.ofExpr pointwise.source pointwise_valid.2.2.2.1} ∪ {A.ofExpr (.var arg) rfl})
    {A.ofExpr pointwise.target pointwise_valid.2.2.2.2} := by
  apply A.ProofTree.rightReplace (Δ := ∅) (Ξ := ∅) pointwise pointwise_valid
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

example : A.Provable
    (parameterCollision.context
      ({A.ofExpr pointwise.source pointwise_valid.2.2.2.1} ∪ {A.ofExpr (.var arg) rfl}))
    (parameterCollision.context {A.ofExpr pointwise.target pointwise_valid.2.2.2.2}) :=
  ⟨B.toA (.instSchema parameterCollision (B.ofA pointwiseProof))⟩

-- An instantiation above an epsilon witness rule is also removed, even if its
-- image contains the old binder name freely.
private def epsilonBody : Expr := Expr.and (.var z) (Expr.eq (.var x) (.var x))
private noncomputable def epsilonProof : A.ProofTree
    {A.ofExpr (Expr.substOne x c epsilonBody) (isFormula_substOne rfl rfl rfl)}
    {A.ofExpr (Expr.substOne x (Expr.epsilon_ (.lam x epsilonBody)) epsilonBody)
      (isFormula_substOne rfl (isTerm_epsilon rfl rfl) rfl)} :=
  .rightEpsilon (Δ := ∅) x epsilonBody c rfl rfl rfl (.hypothesis _)

example : A.Provable
    (collision.context {A.ofExpr (Expr.substOne x c epsilonBody) (isFormula_substOne rfl rfl rfl)})
    (collision.context {A.ofExpr (Expr.substOne x (Expr.epsilon_ (.lam x epsilonBody)) epsilonBody)
      (isFormula_substOne rfl (isTerm_epsilon rfl rfl) rfl)}) :=
  ⟨B.toA (.instSchema collision (B.ofA epsilonProof))⟩

-- The public intermediate results use exactly the same Pure boundary as Ordered.
example {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p) :
    A.Provable (A.context Γ hΓ) (A.context Δ hΔ) ↔
      Pure.Provable (Readback.canonicalContext Γ) (Readback.canonicalContext Δ) :=
  a_iff_pure hΓ hΔ hbΓ hbΔ

end Tests.SCLambdaToPure

-- Guard the architecture as well as the theorem statement: the final proof
-- must actually pass through B → A and A → Pure, without a semantic shortcut.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let (_, deps) := ((CollectAxioms.collect ``Lisa.SCLambdaToPure.ordered_iff_pure).run env).run {}
  for n in [``Lisa.SCLambdaToPure.B.ofOrdered, ``Lisa.SCLambdaToPure.B.toA,
      ``Lisa.SCLambdaToPure.A.ProofTree.instantiate, ``Lisa.SCLambdaToPure.A.toPure] do
    unless deps.visited.contains n do
      throwError "The final reduction bypasses required stage {n}"
  for n in deps.visited do
    if let some i := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[i]!
      if "Lisa.SCLambdaToPure.Reference.".isPrefixOf m.toString then
        throwError "The syntactic reduction depends on reference semantics: {n}"

-- Reject proof placeholders or additional assumptions, not merely semantic imports.
open Lean Elab Command in
run_elab do
  for root in [``Lisa.SCLambdaToPure.ordered_iff_pure, ``Lisa.SCLambdaToPure.a_iff_pure,
      ``Lisa.SCLambdaToPure.ordered_iff_a,
      ``Lisa.SCLambdaToPure.b_iff_pure, ``Lisa.SCLambdaToPure.b_iff_a,
      ``Lisa.SCLambdaToPure.Readback.formula_representation,
      ``Lisa.SCLambdaToPure.Readback.term_representation] do
    for axiomName in ← collectAxioms root do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {root}"
