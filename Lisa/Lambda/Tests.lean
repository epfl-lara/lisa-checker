import Lisa.Lambda

namespace Lisa.Lambda.Tests
private def x : SVar := ⟨⟨"x", 0⟩, prop⟩
private def y : SVar := ⟨⟨"y", 0⟩, prop⟩
private def xi : SVar := ⟨x.id, ind⟩
private def f : Expr := .var ⟨⟨"f", 0⟩, prop >> prop⟩
private def idX := Expr.lam x (.var x)
private def idY := Expr.lam y (.var y)
private def capture := Expr.app (.lam x (.lam y (.var x))) (.var y)
private def eta := Expr.lam x (.app f (.var x))

#guard compareNamed idX idY = some true
#guard compareNamed (.app idX (.var y)) (.var y) = some true
#guard compareNamed eta f = some true
#guard compareNamed capture (.lam x (.var y)) = some true
#guard compareNamed capture (.lam y (.var y)) = some false
#guard compareNamed (.var x) (.var xi) = some false
#guard compareNamed (.app (.var x) (.var y)) idX = none
#guard normalizeNamed (.app (.var x) (.var y)) = none
-- Identical names at different sorts do not shadow each other.
#guard compareNamed (.lam x (.lam xi (.var x))) (.lam y (.lam xi (.var y))) = some true
#guard !(AlphaEq (.lam x (.lam xi (.var x))) (.lam x (.lam xi (.var xi))))

private def mixed : Term (prop >> ind >> prop) := .lam prop (.lam ind (.bound 0))
private def same : Term (prop >> prop >> prop) := .lam prop (.lam prop (.bound 1))
private def argument : Term ind := .app (.free ⟨"h", 0⟩) (.bound (s := prop) 0)
private def crossCapture : Term (prop >> ind) := .app (.lam ind (.lam prop (.bound 0))) argument
private def crossExpected : Term (prop >> ind) := .lam prop (.app (.free ⟨"h", 0⟩) (.bound (s := prop) 1))
private def higher : Term ((ind >> prop) >> ind >> prop) := .lam (ind >> prop) (.bound 0)

#guard normalize mixed = mixed
#guard normalize same = same
#guard normalize crossCapture = crossExpected
#guard normalize (.bound 42 : Term prop) = .bound 42
#guard normalize higher = .lam (ind >> prop) (.lam ind (.app (.bound 0) (.bound (s := ind) 0)))
#guard elaborate mixed.erase = some ⟨_, mixed⟩
#guard elaborate (.bound 42 prop) = some ⟨prop, .bound 42⟩
#guard elaborate (.app (.bound 0 prop) (.bound 0 prop)) = none
#guard compareNameless (.bound 0 prop) (.bound 0 ind) = some false
#guard compareNameless (.bound 0 prop) (.bound 1 prop) = some false
#guard compareNameless crossCapture.erase crossExpected.erase = some true
#guard normalizeNameless crossCapture.erase = some crossExpected.erase

private def samples : List Expr :=
  [.var x, .var y, .var xi, f, idX, idY, eta, .app idX (.var x),
   .app idX (.var y), .app idY (.var x), capture, .lam x (.var y),
   .lam y (.var y), .lam x (.lam xi (.var x)), .lam y (.lam xi (.var y)),
   .lam x (.var ⟨⟨"x", 1⟩, prop⟩), .lam xi (.var xi),
   .lam ⟨⟨"g", 0⟩, ind >> prop⟩ (.var ⟨⟨"g", 0⟩, ind >> prop⟩)]
#guard samples.all fun p => p.sort.isSome
#guard samples.all fun p => samples.all fun q => compareNamed p q = some (decide (normalizeNamed p = normalizeNamed q))
#guard samples.all fun p => match normalizeNamed p with
  | none => false
  | some q => normalizeNamed q = some q

#guard normalizeNamed (.lam x (.var ⟨⟨"x", 1⟩, prop⟩)) =
  some (.lam ⟨⟨"x", 2⟩, prop⟩ (.var ⟨⟨"x", 1⟩, prop⟩))

-- The closed-source reconstruction theorem is derived from substitution.
example (h : interpretNamed p Names.free = some ⟨s, e⟩) (σ : Sub) : e.subst σ = e := subst_of_interpretNamed h σ
example (e f : Term s) : Equiv e f ↔ normalize e = normalize f := equiv_iff_normalize_eq e f
example (p : Expr) : compareNamed p p = some true ↔ p.wellSorted := by
  rw [compareNamed_true]
  exact ⟨And.right, fun h => ⟨AlphaBetaEta.refl p, h⟩⟩

#print axioms normalize_sound
#print axioms equiv_iff_normalize_eq
#print axioms compareNamed_true
#print axioms compareNamed_false
#print axioms normalizeNamed_sound
#print axioms normalizeNamed_idempotent
#print axioms alphaBetaEta_iff_normalizeNamed_eq
end Lisa.Lambda.Tests
