import Lisa.Orthologic.Provability
import Lisa.Orthologic.Comparison
import Tests.OLCongruence

/-! Regression examples for the new LambdaFOL comparison and its constructor
proofs. These exercise the new implementation, not Combined or Quantified. -/
namespace OLComparisonTests
open Lisa Lisa.Orthologic

private def atom (name : String) : SimpleExpr prop := .free ⟨name, 0⟩
private def p := atom "p"
private def q := atom "q"

-- Lattice structure, including unordered conjunctions and negative polarity.
#guard latticesEQ (.conj [p, q]) (.conj [q, p])
#guard latticesLEQ (.conj [p, q]) p
#guard !latticesLEQ p (.conj [p, q])
#guard latticesLEQ (.neg p) (.neg (.conj [p, q]))
#guard latticesEQ (.disj [p, q]) (.disj [q, p])
#guard latticesEQ (.conj []) .top
#guard latticesEQ (.neg (.conj [])) .bot

private def pred (name : String) : SimpleExpr prop :=
  .app (.free (s := ind >> prop) ⟨name, 0⟩) (.bound 0)

-- Universals are monotone; their negations reverse the body comparison.
#guard latticesLEQ (.all (.conj [pred "P", pred "Q"])) (.all (pred "P"))
#guard !latticesLEQ (.all (pred "P")) (.all (.conj [pred "P", pred "Q"]))
#guard latticesLEQ (.neg (.all (pred "P")))
    (.neg (.all (.conj [pred "P", pred "Q"])))
#guard latticesLEQ (.ex (.conj [pred "P", pred "Q"])) (.ex (pred "P"))

private def nest : Nat → SimpleExpr prop → SimpleExpr prop
  | 0, p => p
  | n+1, p => .all (nest n p)

-- No quantifier-depth parameter or bounded search.
#guard latticesLEQ (nest 32 (.conj [p, q])) (nest 32 p)

private def h : SimpleExpr ((prop >> prop) >> prop) := .free ⟨"h", 0⟩
private def f : SimpleExpr (prop >> prop) := .lam prop (.conj [.bound 0, .top])
private def g : SimpleExpr (prop >> prop) := .lam prop (.bound 0)

-- The higher-order case that motivated the substitution-rule change.
#guard latticesEQ (.app h f) (.app h g)
-- Implication alone is insufficient for replacing an application argument.
#guard !latticesEQ (.app h (.lam prop (.conj [.bound 0, p]))) (.app h g)

private def epsilon (body : SimpleExpr prop) : SimpleExpr ind :=
  .app (.const (s := (ind >> prop) >> ind) ⟨"epsilon", 0⟩) (.lam ind body)
private def observe (t : SimpleExpr ind) : SimpleExpr prop :=
  .app (.free (s := ind >> prop) ⟨"P", 0⟩) t

-- Both the outer conjunction and a formula below an epsilon term are compared.
#guard latticesEQ
    (.conj [p, observe (epsilon (.disj [pred "Q", pred "R"]))])
    (.conj [observe (epsilon (.disj [pred "R", pred "Q"])), p])

#guard latticesEQ
    (.equal (.free ⟨"a", 0⟩) (.free ⟨"b", 0⟩))
    (.equal (.free ⟨"b", 0⟩) (.free ⟨"a", 0⟩))

-- Identically spelled symbols of different sorts are not interchangeable.
#guard !latticesEQ
    (.app (.free (s := ind >> prop) ⟨"F", 0⟩) (.bound 0))
    (.app (.free (s := prop >> prop) ⟨"F", 0⟩) (.bound 0))

-- A binder of a different sort does not consume a propositional index.
#guard AlphaEq
    ((SimpleExpr.lam prop (.lam ind (.bound (s := prop) 0))).reify Lambda.Context.empty)
    (.lam ⟨⟨"a", 0⟩, prop⟩ (.lam ⟨⟨"b", 0⟩, ind⟩ (.var ⟨⟨"a", 0⟩, prop⟩)))

-- These are actual Ordered derivations, not merely successful Boolean checks.
noncomputable def quantifiedProjection (p q : SimpleExpr prop) (ρ : Lambda.Context) :
    Derivation.Entails ((SimpleExpr.all (.conj [p, q])).reify ρ) (p.all.reify ρ) :=
  SimpleExpr.all_mono (.conj [p, q]) p (fun ρ => by
    simpa only [SimpleExpr.reify_conj_pair] using
      Derivation.and_left (p.reify_sort ρ) (q.reify_sort ρ)) ρ

noncomputable def negativeQuantifiedProjection (p q : SimpleExpr prop) (ρ : Lambda.Context) :
    Derivation.Entails (p.all.neg.reify ρ) ((SimpleExpr.neg (.all (.conj [p, q]))).reify ρ) :=
  SimpleExpr.neg_all_mono p (.conj [p, q]) (fun ρ => by
    simpa only [SimpleExpr.reify_conj_pair] using
      Derivation.and_left (p.reify_sort ρ) (q.reify_sort ρ)) ρ

private def select : SVar := ⟨⟨"select", 0⟩, (prop >> prop) >> ind⟩
private def observer : SVar := ⟨⟨"observer", 0⟩, ind >> prop⟩

/-- Use the general constructor lemmas for a higher-order argument inside an
individual term: observer(select(λx. x ∧ top)) entails observer(select(λx. x)). -/
noncomputable def higherOrderInsideTerm : Derivation.Entails
    (.app (.var observer) (.app (.var select) OLCongruenceTests.f))
    (.app (.var observer) (.app (.var select) OLCongruenceTests.g)) := by
  let x := OLCongruenceTests.x
  have body : Derivation.Theorem
      ((SubstPair.mk (Expr.and (.var x) Expr.top) (.var x)).pointwiseEq []) :=
    Derivation.iff_intro rfl rfl OLCongruenceTests.bodyForward OLCongruenceTests.bodyBackward
  have compared := Derivation.lam_pointwise x (Expr.and (.var x) Expr.top) (.var x)
    prop [] rfl (by decide) body
  exact Derivation.app_argument ⟨⟨"hole", 0⟩, prop >> prop⟩ (.var observer) (.var select)
    OLCongruenceTests.f OLCongruenceTests.g [x] ind rfl rfl rfl
    (by decide) (by decide) compared

#print axioms quantifiedProjection
#print axioms negativeQuantifiedProjection
#print axioms higherOrderInsideTerm
#print axioms Derivation.app_argument
#print axioms Derivation.app_function
#print axioms Derivation.app_congr
#print axioms Derivation.lam_pointwise

-- Independently evaluate a small propositional fragment in Boolean models.
-- This checks polarity and empty/nested conjunction cases against semantics.
private def truth (v : Identifier → Bool) (p : SimpleExpr prop) : Bool :=
  match p with
  | .free x => v x
  | .top => true
  | .neg p => !truth v p
  | .conj ps => ps.attach.all fun q => truth v q.val
  | _ => false -- the generated test fragment contains none of these constructors
termination_by p.size
decreasing_by
  · simp [SimpleExpr.size]
  · exact SimpleExpr.size_lt_conj q.property

private def samples : List (SimpleExpr prop) :=
  let atoms := [p, q, .top, .bot]
  atoms ++ atoms.map .neg ++ atoms.flatMap (fun a => atoms.flatMap (fun b =>
    [.conj [a, b], .disj [a, b], .conj [a, .disj [a.neg, b]], .conj []]))

#eval show IO Unit from do
  for a in samples do
    for b in samples do
      if latticesLEQ a b then
        for vp in [false, true] do
          for vq in [false, true] do
            let v := fun x => if x.name == "p" then vp else vq
            unless !truth v a || truth v b do
              throw (IO.userError "OL comparison contradicted a Boolean valuation")

end OLComparisonTests
