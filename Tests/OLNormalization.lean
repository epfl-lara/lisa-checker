import Lisa.Orthologic.NormalizationSoundness

/-! Regression tests for the Scala-style LambdaFOL normalizer and its proofs. -/
namespace OLNormalizationTests
open Lisa Lisa.Orthologic

private def atom (name : String) : SimpleExpr prop := .free ⟨name, 0⟩
private def p := atom "p"
private def q := atom "q"
private def r := atom "r"

private def normalizesTo (a b : SimpleExpr s) : Bool :=
  decide ((computeNormalForm a).toTerm = b.toTerm)

#guard normalizesTo (.conj []) .top
#guard normalizesTo (.conj [p]) p
#guard normalizesTo (.conj [.top, p, p]) p
#guard normalizesTo (.neg (.neg p)) p
#guard normalizesTo (.disj [p, .bot]) p
#guard normalizesTo (.conj [p, .neg p]) .bot
#guard normalizesTo (.disj [p, .neg p]) .top
#guard normalizesTo (.conj [p, .disj [p, q]]) p
#guard normalizesTo (.disj [p, .conj [p, q]]) p
#guard normalizesTo (.all .top) .top
#guard normalizesTo (.all .bot) .bot
#guard normalizesTo (.ex .top) .top
#guard normalizesTo (.ex .bot) .bot

-- The surrounding conjunction can select a component of a negative conjunction.
#guard normalizesTo (.conj [p, .disj [p, q], .disj [p, r]]) p
-- Incomparable factors survive: no distributive Boolean simplification is assumed.
#guard !normalizesTo (.conj [p, .disj [p.neg, q]]) (.conj [p, q])

private def pred (name : String) : SimpleExpr prop :=
  .app (.free (s := ind >> prop) ⟨name, 0⟩) (.bound 0)
private def stronger := SimpleExpr.all (.conj [pred "P", pred "Q"])

-- Redundancy detection uses monotonic comparison under quantifiers.
#guard latticesEQ (computeNormalForm (.conj [stronger, .all (pred "P")]))
    (computeNormalForm stronger)

private def h : SimpleExpr ((prop >> prop) >> prop) := .free ⟨"h", 0⟩
private def f : SimpleExpr (prop >> prop) := .lam prop (.conj [.bound 0, .top])
private def g : SimpleExpr (prop >> prop) := .lam prop (.bound 0)
#guard normalizesTo (.app h f) (.app h g)
#guard !latticesEQ (computeNormalForm (.app h (.lam prop (.conj [.bound 0, p]))))
    (computeNormalForm (.app h g))

private def epsilon (body : SimpleExpr prop) : SimpleExpr ind :=
  .app (.const (s := (ind >> prop) >> ind) ⟨"epsilon", 0⟩) (.lam ind body)
private def observe (t : SimpleExpr ind) : SimpleExpr prop :=
  .app (.free (s := ind >> prop) ⟨"Observe", 0⟩) t

-- Formulas nested below individual terms remain accessible to normalization.
#guard normalizesTo (observe (epsilon (.conj [pred "P", .top]))) (observe (epsilon (pred "P")))
#guard normalizesTo (.equal (epsilon (.conj [pred "P", .top])) (epsilon (pred "P"))) .top

private def a : SimpleExpr ind := .free ⟨"a", 0⟩
private def b : SimpleExpr ind := .free ⟨"b", 0⟩
#guard normalizesTo (.equal a a) .top
#guard decide ((computeNormalForm (.equal a b)).toTerm = (computeNormalForm (.equal b a)).toTerm)

-- The orientation key retains implicit argument sorts, even for identical names.
private def fromProp : SimpleExpr ind :=
  .app (.free (s := prop >> ind) ⟨"F", 0⟩) (.free ⟨"x", 0⟩)
private def fromInd : SimpleExpr ind :=
  .app (.free (s := ind >> ind) ⟨"F", 0⟩) (.free ⟨"x", 0⟩)
#guard !latticesEQ fromProp fromInd
#guard decide ((computeNormalForm (.equal fromProp fromInd)).toTerm =
  (computeNormalForm (.equal fromInd fromProp)).toTerm)

-- Structural orientation is independent of printed representations. Exercise
-- every constructor, identifier indices, and sorts hidden by typed application.
private def orderingAtoms : List Lambda.RawTerm :=
  [.bound 0 ind, .bound 1 ind, .bound 0 prop,
   .free ⟨⟨"x", 0⟩, ind⟩, .free ⟨⟨"x", 1⟩, ind⟩, .free ⟨⟨"x", 0⟩, prop⟩,
   .free ⟨⟨"y", 0⟩, ind⟩, .const ⟨⟨"x", 0⟩, ind⟩,
   fromProp.toTerm.erase, fromInd.toTerm.erase]

private def orderingSamples : List Lambda.RawTerm :=
  orderingAtoms ++ orderingAtoms.map (.lam ind) ++ orderingAtoms.map (.lam prop) ++
    orderingAtoms.map (fun p => .app p (.bound 0 ind))

#eval show IO Unit from do
  for a in orderingSamples do
    for b in orderingSamples do
      let ab := StructuralOrder.compareTerms a b
      unless ab == (StructuralOrder.compareTerms b a).swap do
        throw (IO.userError "structural ordering is not symmetric under reversal")
      unless (ab == .eq) == decide (a = b) do
        throw (IO.userError "structural ordering lost a constructor, identifier, or sort")

-- Natural-number indices now compare numerically, rather than as printed text.
#guard StructuralOrder.compareTerms (.bound 2 ind) (.bound 10 ind) == .lt

-- Mixed-sort binding and normalization below a higher-order result.
#guard normalizesTo (.lam prop (.lam ind (.conj [.bound (s := prop) 0, .top])))
    (.lam prop (.lam ind (.bound (s := prop) 0)))
#guard normalizesTo (.lam (prop >> prop) (.app (.bound (s := prop >> prop) 0) (.conj [p, .top])))
    (.lam (prop >> prop) (.app (.bound 0) p))

-- Fresh names introduced by reconstruction never capture an existing free name.
private def collision : SimpleExpr prop := .free ⟨"bound", 0⟩
#guard !normalizesTo (.lam prop (.conj [.bound (s := prop) 0, collision])) g
#guard AlphaEq
    ((computeNormalForm (.lam prop (.lam ind (.conj [.bound (s := prop) 0, .top])))).reify Lambda.Context.empty)
    (.lam ⟨⟨"u", 7⟩, prop⟩ (.lam ⟨⟨"v", 3⟩, ind⟩ (.var ⟨⟨"u", 7⟩, prop⟩)))

-- The generic result is actual Ordered provability in BOTH directions.
example (p : SimpleExpr prop) (ρ : Lambda.Context) :
    Nonempty (Ordered.AlphaBetaEtaProof {(computeNormalForm p).reify ρ} {p.reify ρ}) :=
  (computeNormalForm_sound p).le ρ

example (p : SimpleExpr prop) (ρ : Lambda.Context) :
    Nonempty (Ordered.AlphaBetaEtaProof {p.reify ρ} {(computeNormalForm p).reify ρ}) :=
  (computeNormalForm_sound p).symm.le ρ

#print axioms polarLEQ_sound
#print axioms latticesEQ_sound
#print axioms computeNormalForm_sound
#print axioms normalizedLEQ_sound
#print axioms normalizedEQ_sound

private def truth (v : Identifier → Bool) (p : SimpleExpr prop) : Bool :=
  match p with
  | .free x => v x
  | .top => true
  | .neg p => !truth v p
  | .conj ps => ps.attach.all fun q => truth v q.val
  | _ => false
termination_by p.size
decreasing_by
  · simp [SimpleExpr.size]
  · exact SimpleExpr.size_lt_conj q.property

private def samples : List (SimpleExpr prop) :=
  let atoms := [p, q, r, .top, .bot]
  atoms ++ atoms.map .neg ++ atoms.flatMap (fun a => atoms.flatMap (fun b =>
    [.conj [a, b], .disj [a, b], .neg (.neg a), .conj [a, .disj [a.neg, b]],
      .disj [a, .conj [a.neg, b]], .conj [a, .conj [b, a]], .conj []]))

-- Independent finite-model check, including the nonlocal refinement cases.
#eval show IO Unit from do
  for a in samples do
    let n := computeNormalForm a
    for vp in [false, true] do
      for vq in [false, true] do
        for vr in [false, true] do
          let v := fun x => if x.name == "p" then vp else if x.name == "q" then vq else vr
          unless truth v a == truth v n do
            throw (IO.userError "OL normalization changed a Boolean valuation")

end OLNormalizationTests
