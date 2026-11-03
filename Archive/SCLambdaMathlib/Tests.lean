import Lisa.SCLambdaToPure

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

example : A.ProofTree ∅
    {A.ofExpr (.app (.lam z (.var z)) p) (by rfl)} {A.ofExpr p (by rfl)} := by
  have he : A.ofExpr (s := prop) (.app (.lam z (.var z)) p) (by rfl) = A.ofExpr p (by rfl) := by
    apply (A.ofExpr_eq _ _).mpr
    simpa [Expr.substOne, Expr.subst, Subst.subst, z] using
      AlphaBetaEta.beta z (.var z) p (by rfl)
  exact (congrArg (fun a => A.ProofTree ∅ {a} {A.ofExpr p (by rfl)}) he).mpr (.hypothesis _)

-- Alpha-renaming is also formula identity.
example : A.ofExpr (Expr.forall_ x (Expr.eq (.var x) (.var x))) (by rfl) =
    A.ofExpr (Expr.forall_ y (Expr.eq (.var y) (.var y))) (by rfl) := by
  exact (A.ofExpr_eq _ _).mpr (.alpha (by decide))

-- Quantifier introduction uses freshness of the residual contexts.
example : A.ProofTree ∅ ∅
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

-- Higher-order bound variables really are permitted by the canonical-form theorem.
private def higher : Expr :=
  .app (.lam ⟨⟨"h", 0⟩, prop >> prop⟩
    (.app (.var ⟨⟨"h", 0⟩, prop >> prop⟩) p)) (.lam z (.var z))

example {e : Lambda.Term prop}
    (he : Lambda.interpretNamed higher Lambda.Names.free = some ⟨prop, e⟩) :
    Canonical (Lambda.normalize e) ∧ FirstOrderShape.Formula (Lambda.normalize e) := by
  apply FirstOrderShape.canonical_lamfol he
  · exact ⟨⟨True.intro, .predicate 0 _⟩, True.intro⟩
  · simp [higher, p, z]

-- Readback normalizes before recognizing first-order structure.
example : Readback.readFormula higher = Readback.readFormula p := by
  apply Readback.readFormula_eq
  apply (Lambda.alphaBetaEta_iff_normalizeNamed_eq (s := prop) (by rfl)).mpr
  rfl

-- Complete identifiers are preserved, including equal indices with different names.
example : Readback.variableCode x.id ≠ Readback.variableCode y.id := by
  intro h
  have := Readback.variableCode_injective h
  exact (by decide : x.id ≠ y.id) this

-- Epsilon and genuinely higher-order applications are not silently made into atoms.
example : Readback.readTerm (Expr.epsilon_ (.lam x (Expr.eq (.var x) (.var x)))) = none := by
  apply Option.isNone_iff_eq_none.mp
  native_decide

private def opaqueHigher : Expr :=
  .app (.var ⟨⟨"H", 0⟩, (prop >> prop) >> prop⟩) (.lam z (.var z))

example : Readback.readFormula opaqueHigher = none := by
  apply Option.isNone_iff_eq_none.mp
  native_decide

example : Readback.readFormula (.app p p) = none := by rfl

-- Bound 0 in Lisa means the nearest binder; Mathlib numbers binders from outside.
#guard match Readback.readFormula (Expr.forall_ x (Expr.exists_ y (Expr.eq (.var x) (.var y)))) with
  | some (.all (.imp (.all (.imp (.equal (.var (.inr i)) (.var (.inr j))) .falsum)) .falsum)) =>
      i.val == 0 && j.val == 1
  | _ => false

-- Shadowing picks the inner binder, while an unrelated free name stays free.
#guard match Readback.readFormula (Expr.forall_ x (Expr.exists_ x (Expr.eq (.var x) (.var y)))) with
  | some (.all (.imp (.all (.imp (.equal (.var (.inr i)) (.var (.inl j))) .falsum)) .falsum)) =>
      i.val == 1 && j == Readback.variableCode y.id
  | _ => false

#guard (Readback.readTerm (.app f c)).isSome

-- The connective laws are proved for all sorted inputs, not just these examples.
example : Readback.readFormula (Expr.and p (Expr.neg p)) =
    (do return (← Readback.readFormula p) ⊓ (← Readback.readFormula p).not) := by
  rw [Readback.readFormula_and (by rfl) (by rfl), Readback.readFormula_neg (by rfl)]
  cases Readback.readFormula p <;> rfl

-- Intermediate higher-order symbols are grounded by the total translation;
-- the partial reader above deliberately continues to reject them.
#guard match Translation.readFormula opaqueHigher with
  | some (.imp .falsum .falsum) => true
  | _ => false

#guard (Translation.readTerm (Expr.epsilon_ (.lam x (Expr.eq (.var x) (.var x))))).isSome

-- Grounding does not interfere with higher-order beta reduction or with
-- ordinary first-order constants at the boundary.
example : Translation.readFormula higher = Readback.readFormula p := by
  rw [Translation.readFormula_eq (show AlphaBetaEta higher p from by
    apply (Lambda.alphaBetaEta_iff_normalizeNamed_eq (s := prop) (by rfl)).mpr
    rfl)]
  apply Translation.readFormula_of_firstOrder (by rfl)
  · exact .predicate 0 _
  · simp [p]

example (e : Expr) (he : isFormula e) : (Translation.readFormula e).isSome :=
  Translation.readFormula_total he

example (t u : Expr) (ht : isTerm t) (hu : isTerm u) :
    Translation.formula (A.ofExpr (Expr.eq t u) (isFormula_eq ht hu)) =
      (Translation.term t ht).equal (Translation.term u hu) :=
  Translation.formula_eq t u ht hu

-- The total pipeline also preserves Mathlib's outer-to-inner binder levels.
#guard match Translation.readFormula
    (Expr.forall_ x (Expr.exists_ y (Expr.eq (.var x) (.var y)))) with
  | some (.all (.imp (.all (.imp (.equal (.var (.inr i)) (.var (.inr j))) .falsum)) .falsum)) =>
      i.val == 0 && j.val == 1
  | _ => false

-- Replacing a free individual by an ambient index must shift it under a binder.
example : (Replacement.single x (.bound 0)).apply
    (.lam ind (.free (s := ind) x.id)) = .lam ind (.bound (s := ind) 1) := by decide

-- Abstracting x does not capture a proposition with the same printed identifier.
example : (Replacement.abstract x).apply (.free (s := prop) x.id) = .free x.id := by decide

-- Replacing the outer individual underneath another individual quantifier
-- preserves the inner variable. No beta reduction or eta expansion remains.
private def nestedBody : Lambda.Term prop :=
  .app (.const (s := (ind >> prop) >> prop) ⟨"forall", 0⟩)
    (.lam ind (.app (.app (.const (s := ind >> ind >> prop) ⟨"eq", 0⟩) (.bound 1)) (.bound 0)))

example : Lambda.normalize (nestedBody.instantiate (.free (s := ind) y.id)) =
    nestedBody.instantiate (.free (s := ind) y.id) := by
  apply FirstOrderShape.normalize_instantiate_formula
  · exact .all (.eq (.bound 1) (.bound 0))
  · exact .free _

-- Freshness on A's quotient contexts is preserved by the concrete translation.
example : Pure.Fresh (Readback.variableCode x.id)
    (({A.ofExpr p (by rfl)} : A.Context).image Translation.formula) := by
  apply Translation.fresh x _ rfl
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  exact ⟨p, by rfl, rfl, by simp [p]⟩

-- End-to-end proof transport: the eigenvariable is bound in the conclusion.
private noncomputable def quantifiedReflexivity : A.ProofTree ∅ ∅
    {A.ofExpr (Expr.forall_ x (Expr.eq (.var x) (.var x))) (by rfl)} := by
  simpa using A.ProofTree.rightForall (T := ∅) (Γ := ∅) (Δ := ∅) x
    (Expr.eq (.var x) (.var x)) rfl (by rfl)
    (by simpa using A.ProofTree.refl (T := ∅) (.var x) (by rfl))
    (by intro p hp; simp at hp) (by intro p hp; simp at hp)

example : Pure.Provable ∅ ∅
    {Pure.forall_ (Readback.variableCode x.id)
      ((FirstOrder.Language.Term.var (Readback.variableCode x.id)).equal
        (.var (Readback.variableCode x.id)) : Pure.Formula Readback.language)} := by
  refine ⟨?_⟩
  have h := Translation.toPure quantifiedReflexivity
  simp only [Translation.context, Finset.image_empty, Finset.image_singleton] at h
  rw [Translation.formula_all x _ rfl (by rfl),
    Translation.formula_eq _ _ (by rfl) (by rfl)] at h
  simpa only [Translation.term_var x rfl] using h

-- A cut can mention an unrestricted higher-order formula even when the
-- concluding sequent is wholly first-order.
private noncomputable def higherOrderCut : A.ProofTree ∅ ∅ {A.ofExpr Expr.top rfl} := by
  let h := A.ofExpr opaqueHigher (by rfl)
  have left : A.ProofTree ∅ ∅ (insert h {A.ofExpr Expr.top rfl}) :=
    .weakening .rightTrue (by simp) (by simp)
  have right : A.ProofTree ∅ (insert h ∅) {A.ofExpr Expr.top rfl} :=
    .weakening .rightTrue (by simp) (by simp)
  simpa using A.ProofTree.cut h left right

example : Pure.Provable (L := Readback.language) ∅ ∅ {⊤} := by
  refine ⟨?_⟩
  simpa [Translation.context] using Translation.toPure higherOrderCut

-- Capture avoidance is a theorem about the translation, including substitution
-- beneath a binder whose printed name occurs in the replacement.
example : Translation.formula (A.ofExpr
    (Expr.substOne x (.var y) (Expr.forall_ y (Expr.eq (.var x) (.var y))))
    (isFormula_substOne rfl (by rfl) (by rfl))) =
    Pure.substOne (Readback.variableCode x.id) (Translation.term (.var y) (by rfl))
      (Translation.formula (A.ofExpr (Expr.forall_ y (Expr.eq (.var x) (.var y))) (by rfl))) :=
  Translation.formula_subst x _ _ rfl (by rfl) (by rfl)

-- Exercise the reverse implication of the public theorem. Mathlib represents
-- conjunction using implication and falsity, so this must use the proved
-- logical roundtrip, rather than treating the two syntaxes as alpha-equal.
example : A.Provable ∅ {A.ofExpr p (by rfl)}
    {A.ofExpr (Expr.and p Expr.top) (by rfl)} := by
  classical
  have hp : isFSet {p} := by
    intro e he; obtain rfl := Finset.mem_singleton.mp he; rfl
  have hq : isFSet {Expr.and p Expr.top} := by
    intro e he; obtain rfl := Finset.mem_singleton.mp he; rfl
  have bp : ∀ e ∈ ({p} : Finset Expr), FirstOrderBoundary e := by
    intro e he; obtain rfl := Finset.mem_singleton.mp he
    exact ⟨.predicate 0 _, by simp [p]⟩
  have bq : ∀ e ∈ ({Expr.and p Expr.top} : Finset Expr), FirstOrderBoundary e := by
    intro e he; obtain rfl := Finset.mem_singleton.mp he
    exact ⟨⟨⟨.and, .predicate 0 _⟩, .top⟩, by simp [Expr.and, Expr.top, p]⟩
  have hc (e : Expr) (hs : isFSet {e}) :
      A.context {e} hs = {A.ofExpr e (hs e (Finset.mem_singleton_self e))} := by
    ext q
    simp [A.context, eq_comm]
  have h := (a_iff_pure hp hq bp bq).mpr
  rw [hc p hp, hc (Expr.and p Expr.top) hq] at h
  apply h
  rw [← Translation.context_eq_canonical _ hp bp, ← Translation.context_eq_canonical _ hq bq,
    hc p hp, hc (Expr.and p Expr.top) hq]
  simp only [Translation.context, Finset.image_singleton]
  rw [Translation.formula_and p Expr.top (by rfl) rfl, Translation.formula_top]
  refine ⟨?_⟩
  simpa using Pure.ProofTree.rightAnd (L := Readback.language) (T := ∅)
    (Γ := {Translation.formula (A.ofExpr p (by rfl))}) (Δ := ∅) (Γ₁ := ∅) (Δ₁ := ∅)
    (Translation.formula (A.ofExpr p (by rfl))) ⊤
    (by simpa using Pure.ProofTree.hypothesis (T := ∅) (Translation.formula (A.ofExpr p (by rfl))))
    (by simpa using Pure.ProofTree.rightTrue (L := Readback.language) (T := ∅))

-- A first-order boundary can contain arbitrary higher-order beta redexes.
example : Embedding.Roundtrip (A.ofExpr higher (by rfl)) := by
  apply Embedding.firstOrder_roundtrip (by rfl)
  exact ⟨⟨⟨True.intro, .predicate 0 _⟩, True.intro⟩, by simp [higher, p, z]⟩

-- Schematic instantiation may introduce the original eigenvariable freely.
-- The conclusion must bind a fresh variable instead of capturing that occurrence.
private def rx : Expr := .app (.const (.named "R" (ind >> prop))) (.var x)
private def collision : Instantiation := ⟨.cons z rx .nil, ⟨rfl, trivial⟩⟩

private noncomputable def vacuousAll : A.ProofTree ∅ {A.ofExpr (.var z) (by rfl)}
    {A.ofExpr (Expr.forall_ x (.var z)) (by rfl)} := by
  apply A.ProofTree.rightForall (Γ := {A.ofExpr (.var z) (by rfl)}) (Δ := ∅)
    x (.var z) rfl (by rfl)
  · exact .hypothesis _
  · intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact ⟨.var z, rfl, rfl, by decide⟩
  · intro q hq; simp at hq

private noncomputable def instantiatedAll : B.ProofTree ∅
    {A.ofExpr rx (by rfl)} {A.ofExpr (Expr.forall_ y rx) (by rfl)} := by
  have h := B.ProofTree.instSchema collision (B.ofA vacuousAll)
  simp only [Instantiation.context_singleton] at h
  rw [collision.expression_forall x y rfl (.var z) rfl rfl (by decide),
    Instantiation.expression_ofExpr] at h
  exact h

example : A.Provable ∅ {A.ofExpr rx (by rfl)}
    {A.ofExpr (Expr.forall_ y rx) (by rfl)} := ⟨B.toA instantiatedAll⟩

-- The instantiation can occur below a subsequent ordinary inference.
example : A.Provable ∅
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

private noncomputable def higherInstProof : B.ProofTree ∅
    {A.ofExpr p (by rfl)} {A.ofExpr p (by rfl)} := by
  have h := B.ProofTree.instSchema higherSubst
    (B.ProofTree.hypothesis (T := ∅) (A.ofExpr (.app (.var higherVar) p) (by rfl)))
  simpa only [Instantiation.context_singleton, higherInstance] using h

-- End-to-end: a B proof with a higher-order intermediate formula reaches Pure.
example : Pure.Provable ∅ {Translation.formula (A.ofExpr p (by rfl))}
    {Translation.formula (A.ofExpr p (by rfl))} := by
  exact ⟨by simpa [Translation.context] using B.toPure higherInstProof⟩

-- Simultaneous replacement keeps the free variable in an image intact; a second
-- entry is not recursively applied to the first entry's image.
private def simultaneous : Instantiation :=
  ⟨.cons x (.var y) (.cons y c .nil), ⟨rfl, rfl, trivial⟩⟩

example : simultaneous.expression (A.ofExpr (Expr.eq (.var x) (.var y)) (by rfl)) =
    A.ofExpr (Expr.eq (.var y) c) (by rfl) := by
  rw [Instantiation.expression_ofExpr]
  rfl

end Tests.SCLambdaToPure
