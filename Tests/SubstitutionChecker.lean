import Lisa.Checker.Soundness
import Tests.SubstitutionBinary

/-! Executable checks for simultaneous two-premise substitution. -/
namespace SubstitutionCheckerTests
open Lisa Expr Imported Imported.Checker

private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def y : SVar := ⟨⟨"y", 0⟩, ind⟩
private def p : SVar := ⟨⟨"p", 0⟩, prop⟩
private def q : SVar := ⟨⟨"q", 0⟩, prop⟩
private def f : SVar := ⟨⟨"f", 0⟩, ind >> ind⟩
private def z (s : LSort) : SVar := ⟨⟨"z", 0⟩, s⟩
private def a : Expr := .const (.named "user:A" prop)
private def t : Expr := .const (.named "user:t" ind)
private def u : Expr := .const (.named "user:u" ind)
private def step (pre post : List Expr) (rule : Rule) : Step := ⟨⟨pre, post⟩, rule⟩
private def hyp (e : Expr) : Step := step [e] [e] (.hypothesis e)

private def accepted (name : String) (proof : LinearProof) : IO Unit := do
  match check proof with
  | .ok expected =>
    for page in [1, 7, 65536] do
      match ← SubstitutionBinary.check proof page with
      | .error e => throw (IO.userError s!"{name}: binary rejection: {repr e}")
      | .ok results =>
        let some actual := results[0]? | throw (IO.userError s!"{name}: missing binary result")
        unless results.size = 1 && actual.steps = proof.size &&
            actual.checked.statement = expected.statement &&
            actual.checked.assumptions = expected.assumptions do
          throw (IO.userError s!"{name}: binary conclusion or dependencies changed")
  | .error e => throw (IO.userError s!"{name}: unexpected rejection: {repr e}")

private def rejected (name : String) (proof : LinearProof)
    (expected : CheckError := .atStep 2 .invalidConditions) : IO Unit := do
  match check proof with
  | .error e => unless e = expected do
      throw (IO.userError s!"{name}: expected {repr expected}, got {repr e}")
  | .ok _ => throw (IO.userError s!"{name}: accepted invalid proof")
  for page in [1, 7, 65536] do
    match ← SubstitutionBinary.check proof page with
    | .ok _ => throw (IO.userError s!"{name}: binary checker accepted invalid proof")
    | .error e =>
      match expected with
      | .atStep i cause =>
        unless e.message.startsWith s!"Invalid step {i} " &&
            e.message.endsWith s!"{repr cause}" do
          throw (IO.userError s!"{name}: wrong binary rejection: {repr e}")
      | _ => throw (IO.userError s!"{name}: unexpected test error specification")

-- A predicate context makes the ground substitution visible in the conclusion.
private def ground : SubstRule :=
  ⟨[(⟨t, u⟩, [])], ⟨[x], .app (.const (.named "user:F" (ind >> prop))) (.var x)⟩⟩
private def proposition : SubstRule := ⟨[(⟨a, top⟩, [])], ⟨[p], .var p⟩⟩
private def higher (s : LSort) (left right : Expr) (xs : List SVar) : SubstRule :=
  ⟨[(⟨left, right⟩, xs)], ⟨[z s], .app (.const (.named "user:H" (s >> prop))) (.var (z s))⟩⟩

private def checkBoth (name : String) (r : SubstRule) : IO Unit := do
  accepted (name ++ " left") #[hyp r.source, hyp r.equation,
    step [r.target, r.equation] [r.source] (.leftSubst 0 1 r)]
  accepted (name ++ " right") #[hyp r.source, hyp r.equation,
    step [r.source, r.equation] [r.target] (.rightSubst 0 1 r)]

#eval show IO Unit from do
  checkBoth "individual" ground
  checkBoth "proposition" proposition
  -- With arguments, a hypothesis E ⊢ E is not a valid comparison premise:
  -- its left context contains those arguments. Use an explicit assumed sequent.
  let cases := [
    higher (ind >> ind) (.lam x (.var x)) (.lam x t) [y],
    higher (prop >> prop) (.lam p (.var p)) (.lam p (and (.var p) top)) [p],
    higher ((ind >> ind) >> ind >> ind) (.lam f (.var f)) (.lam f (.var f)) [f, x]]
  for r in cases do
    accepted "function comparison" #[hyp r.source, step [] [r.equation] .assume,
      step [r.source] [r.target] (.rightSubst 0 1 r)]
  let batch : SubstRule := ⟨[(⟨a, top⟩, []), (⟨bot, a⟩, [])],
    ⟨[p, q], and (.var p) (.var q)⟩⟩
  checkBoth "simultaneous batch" batch
  checkBoth "empty batch" ⟨[], ⟨[], a⟩⟩

-- A closed comparison proof, not an assumed equation, also survives the wire
-- format. Check both directions of substitution with a proposition argument.
#eval show IO Unit from do
  let r := higher (prop >> prop) (.lam p (.var p)) (.lam p (and (.var p) top)) [p]
  accepted "closed higher-order right" #[hyp r.source, step [] [r.equation] .restateTrue,
    step [r.source] [r.target] (.rightSubst 0 1 r)]
  accepted "closed higher-order left" #[hyp r.source, step [] [r.equation] .restateTrue,
    step [r.target] [r.source] (.leftSubst 0 1 r)]

-- Comparison parameters can occur in the first premise and final sequent.
#eval show IO Unit from do
  let base := higher (prop >> prop) (.lam p (.var p)) (.lam p (and (.var p) top)) [p]
  let r := { base with context := ⟨base.context.params, and (.var p) base.context.body⟩ }
  accepted "parameter in first premise" #[hyp r.source, step [] [r.equation] .assume,
    step [r.source] [r.target] (.rightSubst 0 1 r)]
  accepted "nonempty comparison contexts" #[hyp r.source, step [a] [r.equation, top] .assume,
    step [r.source, a] [r.target, top] (.rightSubst 0 1 r)]
  rejected "parameter in comparison assumptions" #[hyp r.source,
    step [.var p] [r.equation] .assume,
    step [r.source, .var p] [r.target] (.rightSubst 0 1 r)]
  rejected "parameter in comparison residual conclusions" #[hyp r.source,
    step [] [r.equation, .var p] .assume,
    step [r.source] [r.target, .var p] (.rightSubst 0 1 r)]
  rejected "comparison formula absent" #[hyp r.source, hyp a,
    step [r.source, a] [r.target, a] (.rightSubst 0 1 r)]
  rejected "invalid second reference" #[hyp r.source, hyp a,
    step [r.source] [r.target] (.rightSubst 0 5 r)] (.atStep 2 (.invalidReference 5))
  -- The malformed pointwise comparisons are still formulas; rejection must
  -- come from the rule's independent-parameter checks.
  let badFree := higher (ind >> ind) (.lam y (.var y)) (.lam y (.var x)) [x]
  let badDuplicate := higher (ind >> ind >> ind)
    (.lam x (.lam y (.var x))) (.lam x (.lam y (.var y))) [x, x]
  for bad in [badFree, badDuplicate] do
    rejected "invalid comparison parameters" #[hyp bad.source, step [] [bad.equation] .assume,
      step [bad.source] [bad.target] (.rightSubst 0 1 bad)]

-- Both premises' imported dependencies must survive the inference.
#eval show IO Unit from do
  let first := step [] [ground.source] .assume
  let second := step [] [ground.equation] .assume
  let proof := #[first, second, step [] [ground.target] (.rightSubst 0 1 ground)]
  accepted "both imported dependencies" proof
  match check proof with
  | .error e => throw (IO.userError s!"two-premise import: {repr e}")
  | .ok result =>
    unless result.assumptions = {first.statement, second.statement} do
      throw (IO.userError "substitution lost a premise's imported dependency")

-- Signed references address external imports; neither dependency may be lost.
#eval show IO Unit from do
  let imports : Array Statement := #[⟨[], [ground.source]⟩, ⟨[], [ground.equation]⟩]
  let proof := #[step [] [ground.target] (.rightSubst (-1) (-2) ground)]
  for page in [1, 7, 65536] do
    match ← SubstitutionBinary.check proof page imports with
    | .error e => throw (IO.userError s!"binary external premises: {repr e}")
    | .ok results =>
      let some result := results[0]? | throw (IO.userError "missing binary external result")
      unless result.imports = 2 && result.checked.statement = ⟨[], [ground.target]⟩ &&
          result.checked.assumptions = imports.toList.toFinset do
        throw (IO.userError "binary substitution lost an external premise")

-- Simultaneous replacement includes duplicate context parameters and
-- replacement expressions mentioning another hole.
#eval show IO Unit from do
  checkBoth "overlapping replacements" ⟨[(⟨.var q, a⟩, []), (⟨bot, top⟩, [])],
    ⟨[p, q], and (.var p) (.var q)⟩⟩
  checkBoth "duplicate context parameters" ⟨[(⟨a, top⟩, []), (⟨bot, a⟩, [])], ⟨[p, p], .var p⟩⟩
  let predicate : SVar := ⟨⟨"P", 0⟩, ind >> prop⟩
  let left := Expr.lam x (eq (.var x) t)
  let right := Expr.lam y (eq (.var y) u)
  let r : SubstRule := ⟨[(⟨left, right⟩, [x])],
    ⟨[predicate], forall_ x (.app (.var predicate) (.var x))⟩⟩
  accepted "replacement under binder" #[hyp r.source, step [] [r.equation] .assume,
    step [r.source] [r.target] (.rightSubst 0 1 r)]

end SubstitutionCheckerTests
