import Lisa.Checker.Soundness

namespace CheckerIntegrationTests
open Lisa Expr Imported.Checker

private def p := Expr.var ⟨⟨"p", 0⟩, prop⟩
private def q := Expr.var ⟨⟨"q", 0⟩, prop⟩
private def r := Expr.var ⟨⟨"r", 0⟩, prop⟩
private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def y : SVar := ⟨⟨"y", 4⟩, ind⟩
private def z : SVar := ⟨⟨"z", 0⟩, prop⟩
private def pred (name : String) (v : SVar) : Expr :=
  .app (.var ⟨⟨name, 0⟩, ind >> prop⟩) (.var v)
private def observe (e : Expr) : Expr := .app (.var ⟨⟨"P", 0⟩, ind >> prop⟩) e
private def eps (body : Expr) : Expr := epsilon_ (.lam x body)
private def step (pre post : List Expr) (rule : Rule) : Step := ⟨⟨pre, post⟩, rule⟩

private def accepted (name : String) (proof : LinearProof) : IO Unit := do
  match check proof with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"{name}: {repr e}")

#eval show IO Unit from do
  -- Both stages are required: beta exposes conjunction, OL removes top.
  let beta := Expr.app (.lam z (and (.var z) top)) p
  accepted "beta then OL" #[step [p] [beta] (.hypothesis p)]
  let allPQ := forall_ x (and (pred "P" x) (pred "Q" x))
  let allP := forall_ y (pred "P" y)
  accepted "quantifier monotonicity" #[step [] [allPQ] .assume,
    step [] [allP] (.weakening 0)]
  accepted "existential monotonicity" #[step [] [exists_ x (and (pred "P" x) (pred "Q" x))] .assume,
    step [] [exists_ y (pred "P" y)] (.weakening 0)]
  let a := observe (eps (or (pred "Q" x) (pred "R" x)))
  let b := observe (eps (or (pred "R" x) (pred "Q" x)))
  accepted "formulas inside epsilon terms" #[step [and p a] [and b p] (.hypothesis (and p a))]
  let h := Expr.var ⟨⟨"h", 0⟩, (prop >> prop) >> prop⟩
  let f := Expr.app h (.lam z (and (.var z) top))
  let g := Expr.app h (.lam z (.var z))
  accepted "higher-order argument" #[step [f] [g] (.hypothesis f)]
  -- Wire order and duplicates cannot affect the finite-set certificate.
  accepted "permuted duplicate contexts" #[step [p, q, p] [r, p, r] .assume,
    step [q, p] [p, r] (.restate 0)]
  match check #[step [p] [q] (.hypothesis p)] with
  | .error (.atStep 0 .invalidConditions) => pure ()
  | _ => throw (IO.userError "unrelated atoms matched")
  match check #[step [] [.app p p] .restateTrue] with
  | .error (.atStep 0 .illSortedConclusion) => pure ()
  | _ => throw (IO.userError "malformed conclusion accepted")
  -- Distributivity is provable in Ordered, but this OL comparison rejects it.
  -- Discharge must retain that unchecked assumption, even when the reference
  -- relation identifies it with the proved truth sequent.
  let dist := iff (and p (or q r)) (or (and p q) (and p r))
  let assumption : Statement := ⟨[], [dist]⟩
  unless !(Statement.testSame assumption ⟨[], [top]⟩).ok do
    throw (IO.userError "distributivity no longer exercises incomplete comparison")
  match check #[⟨assumption, .assume⟩, step [] [top] .restateTrue,
      ⟨assumption, .discharge 0 1⟩] with
  | .ok checked =>
    unless checked.assumptions = {assumption} do
      throw (IO.userError "discharge silently removed an unchecked assumption")
  | .error e => throw (IO.userError s!"discharge: {repr e}")
  let identity := #[step [p] [p] (.hypothesis p), step [] [imp p p] (.rightImp 0 p p)]
  match checkClosed identity ⟨[], [imp p p]⟩ with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"closed identity: {repr e}")

example (checked : ClosedChecked ProofRelation ⟨[], [imp p p]⟩) :
    Nonempty (Ordered.AlphaBetaEtaProof ∅ {imp p p}) := checked.sound

-- These certificates are grounded in Ordered αβη, with no extra logic axioms.
#print axioms Checked.sound
#print axioms ClosedChecked.sound
#print axioms Statement.same_formula
#print axioms Imported.ProofTree.weakenAssumptions

run_cmd do
  let env ← Lean.getEnv
  for name in [`Imported.Checker.Matching, `CheckerOrder, `OrderReduction,
      `Lisa.Combined.Replay.leq, `ExpressionOrder.leq, `Ortholattice] do
    if env.contains name then
      throwError "The checker still imports the retired interface {name}"

end CheckerIntegrationTests
