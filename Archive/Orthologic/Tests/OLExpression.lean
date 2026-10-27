import Lisa.Orthologic.ExpressionSoundness

/-! End-to-end named-input tests: alpha-beta-eta, logical lowering, OL
normalization, comparison, reconstruction, and malformed-input behavior. -/
namespace OLExpressionTests
open Lisa

private def varExpr (name : String) (s : LSort) (idx : Nat := 0) : Expr :=
  .var ⟨⟨name, idx⟩, s⟩
private def p := varExpr "p" prop
private def q := varExpr "q" prop
private def r := varExpr "r" prop
private def a := varExpr "a" ind
private def b := varExpr "b" ind
private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def y : SVar := ⟨⟨"y", 7⟩, ind⟩
private def z : SVar := ⟨⟨"z", 0⟩, prop⟩
private def pred (name : String) (x : SVar) : Expr := .app (varExpr name (ind >> prop)) (.var x)

#guard Lisa.Orthologic.normalize (p.and Expr.top) = some p
#guard Lisa.Orthologic.normalize ((p.or q).and p) = some p
#guard Lisa.Orthologic.isSame (p.and q) (q.and p) = some true
#guard Lisa.Orthologic.isSame (p.or q) (q.or p) = some true
#guard Lisa.Orthologic.isSame p p.neg.neg = some true
#guard Lisa.Orthologic.isSame (p.and p.neg) Expr.bot = some true
#guard Lisa.Orthologic.isSame (p.or p.neg) Expr.top = some true
#guard Lisa.Orthologic.isSame (p.imp q) (p.neg.or q) = some true
#guard Lisa.Orthologic.isSame (p.iff q) ((p.imp q).and (q.imp p)) = some true
#guard Lisa.Orthologic.isSame (p.iff q) (q.iff p) = some true
#guard Lisa.Orthologic.isSame (p.and (q.or r)) ((p.and q).or (p.and r)) = some false
#guard Lisa.Orthologic.isImplying (p.and q) p = some true
#guard Lisa.Orthologic.isImplying p (p.and q) = some false

-- Both stages are needed: beta exposes a conjunction, OL removes truth.
#guard Lisa.Orthologic.normalize (.app (.lam z ((Expr.var z).and Expr.top)) p) = some p
#guard Lisa.Orthologic.isSame (.lam z (.app (varExpr "f" (prop >> prop)) (.var z)))
    (varExpr "f" (prop >> prop)) = some true
#guard Lisa.Orthologic.normalize (.lam x (pred "P" x)) = Lisa.Orthologic.normalize (.lam y (pred "P" y))

-- Quantifier monotonicity, existential duality, and simplification.
private def allP := Expr.forall_ x (pred "P" x)
private def allPQ := Expr.forall_ y ((pred "P" y).and (pred "Q" y))
#guard Lisa.Orthologic.isImplying allPQ allP = some true
#guard Lisa.Orthologic.isImplying allP allPQ = some false
#guard Lisa.Orthologic.isSame (allPQ.and allP) allPQ = some true
#guard Lisa.Orthologic.isImplying (Expr.exists_ x ((pred "P" x).and (pred "Q" x)))
    (Expr.exists_ y (pred "P" y)) = some true
#guard Lisa.Orthologic.isSame (Expr.exists_ x (pred "P" x))
    (Expr.neg (Expr.forall_ y (Expr.neg (pred "P" y)))) = some true
#guard Lisa.Orthologic.normalize (Expr.forall_ x Expr.top) = some Expr.top
#guard Lisa.Orthologic.isSame (Expr.exists_ x Expr.bot) Expr.bot = some true
#guard Lisa.Orthologic.isSame (Expr.exists_ x Expr.top) Expr.top = some true
-- A predicate argument without an explicit lambda is eta-expanded first.
#guard Lisa.Orthologic.isSame (.app (.const (.named "forall" ((ind >> prop) >> prop)))
    (varExpr "P" (ind >> prop))) allP = some true

-- Equality operands are normalized, then compared symmetrically.
#guard Lisa.Orthologic.isSame (a.eq b) (b.eq a) = some true
#guard Lisa.Orthologic.normalize (a.eq a) = some Expr.top
private def eps (body : Expr) := Expr.epsilon_ (.lam x body)
private def observe (e : Expr) := Expr.app (varExpr "Observe" (ind >> prop)) e
#guard Lisa.Orthologic.isSame (observe (eps ((pred "P" x).or (pred "Q" x))))
    (observe (eps ((pred "Q" x).or (pred "P" x)))) = some true
#guard Lisa.Orthologic.isSame (a.and (observe (eps (pred "P" x)))) p = none
#guard Lisa.Orthologic.isSame (p.and (observe (eps ((pred "P" x).or (pred "Q" x)))))
    ((observe (eps ((pred "Q" x).or (pred "P" x)))).and p) = some true
#guard Lisa.Orthologic.isSame (eps (pred "P" x)) (eps ((pred "P" x).and (pred "Q" x))) = some false

-- Normalization inside genuinely higher-order arguments.
private def h := varExpr "h" ((prop >> prop) >> prop)
#guard Lisa.Orthologic.isSame (.app h (.lam z ((Expr.var z).and Expr.top)))
    (.app h (.lam z (.var z))) = some true
#guard Lisa.Orthologic.isSame (.app h (.lam z ((Expr.var z).and p)))
    (.app h (.lam z (.var z))) = some false
#guard Lisa.Orthologic.isSame (.lam z (.lam x ((Expr.var z).and Expr.top)))
    (.lam z (.lam y (.var z))) = some true
-- Partial logical applications are eta-expanded and compared at function sort.
#guard Lisa.Orthologic.isSame (.app (.const (.named "and" (prop >> prop >> prop))) Expr.top)
    (.lam z (.var z)) = some true

-- Names that resemble reification's generated binders remain free.
private def collision := varExpr "x" prop 1
#guard Lisa.Orthologic.isSame (.lam z ((Expr.var z).and collision)) (.lam z (.var z)) = some false
#guard Lisa.Orthologic.isSame (.lam x (varExpr "x" prop)) (.lam y (varExpr "x" prop)) = some true
#guard Lisa.Orthologic.isSame (.lam x (.lam y (.var x))) (.lam x (.lam y (.var y))) = some false
#guard Lisa.Orthologic.isSame (.app (.lam z (.lam x (.var z))) (pred "P" x))
    (.lam y (pred "P" x)) = some true

-- The complete identifier AND sort determine whether a symbol is logical.
#guard Lisa.Orthologic.isSame (.const ⟨⟨"top", 1⟩, prop⟩) Expr.top = some false
#guard Lisa.Orthologic.isSame (.const ⟨⟨"top", 0⟩, ind⟩) Expr.top = some false
#guard Lisa.Orthologic.isSame (.app (.app (.const ⟨⟨"and", 1⟩, prop >> prop >> prop⟩) p) Expr.top) p = some false
#guard Lisa.Orthologic.isSame (.app (.app (.const ⟨⟨"and", 0⟩, ind >> prop >> prop⟩) a) Expr.top) p = some false
#guard Lisa.Orthologic.isSame (.app (varExpr "and" (prop >> prop >> prop)) p)
    (.app (.const (.named "and" (prop >> prop >> prop))) p) = some false

private def malformed := Expr.app p q
#guard Lisa.Orthologic.normalize malformed = none
#guard Lisa.Orthologic.isSame malformed malformed = none
#guard Lisa.Orthologic.isSame p malformed = none
#guard Lisa.Orthologic.isSame malformed p = none
#guard Lisa.Orthologic.isSame a p = some false
#guard Lisa.Orthologic.isImplying a a = none
#guard Lisa.Orthologic.isImplying malformed p = none
#guard Lisa.Orthologic.isImplying p a = none

-- Public soundness theorems target the existing proof system, not a new relation.
example (hp : isFormula p) (h : Lisa.Orthologic.normalize p = some q) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) ∧
      Nonempty (Ordered.AlphaBetaEtaProof {q} {p}) := Lisa.Orthologic.normalize_formula_sound hp h

example (h : Lisa.Orthologic.isImplying p q = some true) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) := Lisa.Orthologic.isImplying_sound h

#print axioms Lisa.Orthologic.SimpleExpr.ofTerm_sound
#print axioms Lisa.Orthologic.normalize_sound
#print axioms Lisa.Orthologic.isSame_sound
#print axioms Lisa.Orthologic.isImplying_sound

private def truth (v : Identifier → Bool) : Expr → Option Bool
  | .var x => some (v x.id)
  | .const ⟨⟨"top", 0⟩, _⟩ => some true
  | .const ⟨⟨"bot", 0⟩, _⟩ => some false
  | .app (.const ⟨⟨"not", 0⟩, _⟩) p => do return !(← truth v p)
  | .app (.app (.const ⟨⟨"and", 0⟩, _⟩) p) q => do return (← truth v p) && (← truth v q)
  | .app (.app (.const ⟨⟨"or", 0⟩, _⟩) p) q => do return (← truth v p) || (← truth v q)
  | .app (.app (.const ⟨⟨"imp", 0⟩, _⟩) p) q => do return !(← truth v p) || (← truth v q)
  | .app (.app (.const ⟨⟨"iff", 0⟩, _⟩) p) q => do return (← truth v p) == (← truth v q)
  | _ => none

private def samples : List Expr :=
  let atoms := [p, q, r, Expr.top, Expr.bot]
  atoms ++ atoms.map Expr.neg ++ atoms.flatMap (fun a => atoms.flatMap (fun b =>
    [a.and b, a.or b, a.imp b, a.iff b]))

-- Independent Boolean evaluation checks all connective expansions and the
-- reconstructed output: 110 expressions under all eight valuations.
#eval show IO Unit from do
  for e in samples do
    let some n := Lisa.Orthologic.normalize e
      | throw (IO.userError "Normalization rejected a well-sorted sample")
    unless Lisa.Orthologic.isSame e n == some true do
      throw (IO.userError "Normalized output no longer compares equal to its input")
    for vp in [false, true] do
      for vq in [false, true] do
        for vr in [false, true] do
          let v := fun x => if x.name == "p" then vp else if x.name == "q" then vq else vr
          let some expected := truth v e | throw (IO.userError "Sample is not propositional")
          unless truth v n == some expected do
            throw (IO.userError "The named pipeline changed a Boolean valuation")

end OLExpressionTests
