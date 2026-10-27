import Lisa.Orthologic.Lowering
import Lisa.Orthologic.Normalization
import Lisa.Lambda.NamedDecision

/-! The public LambdaFOL pipeline: alpha-beta-eta canonicalization, extended OL
normalization, then lattice comparison. No stage uses fuel. Soundness is proved
in `ExpressionSoundness`; this file contains only executable definitions.
-/

namespace Lisa.Orthologic

/-- Elaborate once, canonicalize by alpha-beta-eta, then normalize by OL. -/
def prepare (p : Expr) : Option SomeExpr :=
  (Lambda.interpretNamed p Lambda.Names.free).map fun ⟨s, e⟩ =>
    ⟨s, computeNormalForm (SimpleExpr.ofTerm (Lambda.normalize e))⟩

/-- Reconstruct named output. `none` means the input is ill-sorted. The result
is provably interchangeable with the input; its spelling is not a unique key
for OL equivalence, which is tested by `isSame`. -/
def normalize (p : Expr) : Option Expr :=
  (prepare p).map fun ⟨_, e⟩ => e.reify Lambda.Context.empty

/-- Compare normalized expressions, including commutativity. Ill-sorted inputs
give `none`; different sorts give `some false`. A negative answer does not claim
unprovability in the proof system. -/
def isSame (p q : Expr) : Option Bool := do
  let ⟨s, p⟩ ← prepare p
  let ⟨t, q⟩ ← prepare q
  if h : t = s then some (latticesEQ p (h ▸ q)) else some false

/-- Compare normalized formulas in the implication direction. Return `none`
unless both inputs have proposition sort, including for well-sorted terms. -/
def isImplying (p q : Expr) : Option Bool := do
  let ⟨.prop, p⟩ ← prepare p | none
  let ⟨.prop, q⟩ ← prepare q | none
  some (latticesLEQ p q)

end Lisa.Orthologic
