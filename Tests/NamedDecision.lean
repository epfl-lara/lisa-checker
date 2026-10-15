import Lisa.Lambda.NamedDecision

namespace Lisa.Tests.NamedDecision

open Lisa.Lambda

private def x : SVar := ⟨⟨"x", 0⟩, prop⟩
private def y : SVar := ⟨⟨"y", 0⟩, prop⟩
private def xInd : SVar := ⟨x.id, ind⟩
private def f : Expr := .var ⟨⟨"f", 0⟩, prop >> prop⟩
private def idX := Expr.lam x (.var x)
private def idY := Expr.lam y (.var y)
private def capture := Expr.app (.lam x (.lam y (.var x))) (.var y)
private def betaEta := Expr.lam x (.app idY (.app f (.var x)))

#guard compareNamed idX idY = some true
#guard compareNamed (.var x) (.var y) = some false
#guard compareNamed (.var x) (.var xInd) = some false
#guard compareNamed (.app idX (.var y)) (.var y) = some true
#guard compareNamed capture (.lam x (.var y)) = some true
#guard compareNamed capture idY = some false
#guard compareNamed betaEta f = some true
#guard compareNamed (.app betaEta (.var y)) (.app f (.var y)) = some true
#guard compareNamed (.lam x (.app f (.var x))) f = some true
#guard compareNamed (.lam x (.var xInd)) (.lam y (.var xInd)) = some true
#guard compareNamed (.lam x (.lam y (.var x))) (.lam x (.lam y (.var y))) = some false
#guard compareNamed (.app (.var x) (.var y)) (.var x) = none
#guard compareNamed (.var x) (.app f (.var xInd)) = none
#guard compareNamed (.app (.var x) (.var y)) (.app (.var x) (.var y)) = none
#guard normalizeNamed (.app (.var x) (.var y)) = none
#guard normalizeNamed idX = normalizeNamed idY
#guard normalizeNamed betaEta = normalizeNamed f
#guard normalizeNamed capture ≠ normalizeNamed idY

private def p : SortedExpr prop := ⟨.var x, rfl⟩
private def q : SortedExpr prop := ⟨.var y, rfl⟩
private def pBeta : SortedExpr prop := ⟨.app idX (.var x), rfl⟩

#guard decide (p.Equivalent pBeta)
#guard !decide (p.Equivalent q)

private def freeX1 : Term [] (prop >> prop) := .lam (.free ⟨"x", 1⟩)

#guard freeX1.reify Context.empty =
  .lam ⟨⟨"x", 2⟩, prop⟩ (.var ⟨⟨"x", 1⟩, prop⟩)
#guard elaborate [] ((freeX1.reify Context.empty).toNameless []) = some ⟨_, freeX1⟩

private def samples : List Expr :=
  [.var x, .var y, .var xInd, f, idX, idY, capture, betaEta,
    .app idX (.var x), .app idY (.var y), .app betaEta (.var y), .app f (.var y),
    .lam x (.lam y (.var x)), .lam x (.lam y (.var y)),
    .lam xInd (.var x), .lam y (.var x),
    .app (.var x) (.var y), .app f (.var xInd)]

/-- Compare independent executable views and require idempotence of every successful readback. -/
private def agrees (p q : Expr) : Bool :=
  match normalizeNamed p, normalizeNamed q with
  | some p', some q' => compareNamed p q == some (p' == q')
  | _, _ => compareNamed p q == none

#guard samples.length = 18
#guard samples.all fun p => samples.all fun q => agrees p q
#guard samples.all fun p =>
  match normalizeNamed p with
  | none => true
  | some q => normalizeNamed q == some q

example {e f : Term Γ s} (h : Equiv e f) (ρ : Context Γ) :
    Conversion (e.reify ρ) (f.reify ρ) := h.reify ρ

example {p q : Expr} (hp : p.hasSort s) : compareNamed p q = some true ↔ Conversion p q :=
  compareNameless_iff_conversion hp

example {p q : Expr} (h : compareNamed p q = some true) : Conversion p q :=
  conversion_of_compareNameless h

example {p q : Expr} (hp : p.hasSort s) : Conversion p q ↔ normalizeNamed p = normalizeNamed q :=
  conversion_iff_normalizeNamed_eq hp

example {p q : Expr} (h : normalizeNamed p = some q) : normalizeNamed q = some q :=
  normalizeNamed_idempotent h

example (e : Term [] s) :
    elaborate [] ((e.reify Context.empty).toNameless []) = some ⟨s, e⟩ := elaborate_reify e

#print axioms interpretNamed_reify
#print axioms Equiv.reify
#print axioms conversion_of_compareNameless
#print axioms compareNamed_true
#print axioms compareNamed_false
#print axioms normalizeNamed_sound
#print axioms conversion_iff_normalizeNamed_eq
#print axioms normalizeNamed_idempotent

end Lisa.Tests.NamedDecision
