import Lisa.Lambda.NamedDecision

namespace Lisa.Tests.NamedIntegration

open Lisa.Lambda

private def x : SVar := ⟨⟨"x", 0⟩, prop⟩
private def y : SVar := ⟨⟨"y", 0⟩, prop⟩
private def y1 : SVar := ⟨⟨"y", 1⟩, prop⟩
private def xInd : SVar := ⟨x.id, ind⟩
private def f : Expr := .var ⟨⟨"f", 0⟩, prop >> prop⟩

private def typed (e : Expr) := interpretNamed e (Names.free : Names)

#guard typed (.var x) = some ⟨prop, .free x.id⟩
#guard typed (.lam x (.var x)) = some ⟨prop >> prop, .lam prop (.bound 0)⟩
#guard typed (.lam x (.lam x (.var x))) =
  some ⟨prop >> prop >> prop, .lam prop (.lam prop (.bound 0))⟩
#guard typed (.lam x (.lam y (.var x))) =
  some ⟨prop >> prop >> prop, .lam prop (.lam prop (.bound 1))⟩
#guard typed (.lam xInd (.var x)) = some ⟨ind >> prop, .lam ind (.free x.id)⟩
#guard typed (.app (.var x) (.var y)) = none
#guard typed (.app f (.var xInd)) = none
#guard typed (.lam x (.app f (.var xInd))) = none

/-- Exercise freshening when the replacement contains the original binder. -/
private def capture := Expr.substOne x (.var y) (.lam y (.var x))

#guard capture = .lam y1 (.var y)
#guard typed capture = some ⟨prop >> prop, .lam prop (.free y.id)⟩
#guard typed capture ≠ typed (.lam y (.var y))

/-- Freshening an outer binder must also avoid capture by a nested binder of that fresh name. -/
private def nestedCapture := Expr.substOne x (.var y)
  (.lam y (.lam y1 (.app (.var ⟨⟨"h", 0⟩, prop >> prop >> prop⟩) (.var y))))

#guard typed nestedCapture = typed
  (.lam y1 (.lam ⟨⟨"y", 2⟩, prop⟩
    (.app (.var ⟨⟨"h", 0⟩, prop >> prop >> prop⟩) (.var y1))))

#guard typed (Expr.substOne x (.var y) (.lam x (.var x))) = typed (.lam x (.var x))
#guard typed (Expr.substOne x (.var y) (.lam xInd (.var x))) =
  typed (.lam xInd (.var y))
#guard typed (Expr.substOne xInd (.var xInd) (.lam x (.var xInd))) =
  typed (.lam x (.var xInd))

private def duplicates : Subst := .cons x (.var y) (.cons x (.var xInd) .nil)

#guard duplicates.find? x = some (.var y)
#guard (duplicates.without x).find? x = none
#guard (duplicates.insert x (.var x)).find? x = some (.var x)
#guard (Subst.subst duplicates (.lam x (.var x))).sort = some (prop >> prop)

/-- Check named substitution against typed instantiation across a mixed syntax corpus. -/
private def singleCheck (x : SVar) (body arg : Expr) : Bool :=
  match typed arg with
  | none => true
  | some ⟨s, a⟩ =>
      if h : s = x.sort then
        typed (Expr.substOne x arg body) ==
          (interpretNamed body ((Names.free : Names).bind x)).map
            (Packed.subst (Term.single (h ▸ a)))
      else true

private def samples : List Expr :=
  [.var x, .var y, .var y1, .var xInd, f,
    .lam x (.var x), .lam y (.var x), .lam x (.lam y (.var x)),
    .lam y (.lam y1 (.var y)), .lam y1 (.lam y (.var y1)),
    .lam xInd (.var x), .lam x (.var xInd),
    .app f (.var x), .app f (.var y),
    .app (.lam x (.var x)) (.var y),
    .app (.var x) (.var y), .app f (.var xInd),
    .lam x (.app f (.var xInd))]

#guard samples.length = 18
#guard [x, y, y1, xInd].all fun x =>
  samples.all fun body => samples.all fun arg => singleCheck x body arg
#guard samples.all fun e => (typed e).map (fun p => p.1) == e.sort

example (e : Expr) (σ : Subst) (η θ : Names) (h : Represents σ η θ e.freeVars) :
    interpretNamed (σ.subst e) η = interpretNamed e θ :=
  interpretNamed_namedSubst e σ η θ h

example (x : SVar) (body arg : Expr) (η : Names) (a : Term x.sort)
    (ha : interpretNamed arg η = some ⟨x.sort, a⟩) :
    interpretNamed (Expr.substOne x arg body) η =
      (interpretNamed body (η.bind x)).map (Packed.subst (Term.single a)) :=
  interpretNamed_substOne x body arg η a ha

example (h : AlphaBetaEta p q) (η : Names) :
    ResultEquiv (interpretNamed p η) (interpretNamed q η) :=
  interpretNamed_alphaBetaEta h η

#guard compareNamed (.app (.lam x (.lam y (.var x))) (.var y)) capture = some true
#guard compareNamed (.lam x (.app f (.var x))) f = some true

/-- AlphaBetaEta still covers malformed bodies; the intrinsic boundary rejects both sides. -/
example : ResultEquiv
    (typed (.app (.lam x (.app (.var x) (.var x))) (.var y)))
    (typed (.app (.var y) (.var y))) :=
  interpretNamed_alphaBetaEta (.beta x (.app (.var x) (.var x)) (.var y) rfl) Names.free

example : ¬ AlphaBetaEta (.var x) (.var y) :=
  ((compareNamed_false).mp (by decide)).2.2

example : AlphaEq (.lam x (.var x)) (.lam y (.var y)) ↔
    typed (.lam x (.var x)) = typed (.lam y (.var y)) :=
  alpha_iff_interpretNamed_eq rfl rfl

#print axioms interpretNamed_namedSubst
#print axioms interpretNamed_substOne
#print axioms interpretNamed_alpha
#print axioms alpha_iff_interpretNamed_eq
#print axioms interpretNamed_alphaBetaEta
#print axioms compareNamed_true
#print axioms compareNamed_false

end Lisa.Tests.NamedIntegration
