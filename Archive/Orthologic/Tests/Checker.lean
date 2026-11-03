import Tests.CheckerModel

open Lisa Expr Imported Imported.Checker

private def a : Expr := .const (.named "A" prop)
private def b : Expr := .const (.named "B" prop)
private def c : Expr := .const (.named "C" prop)
private def t : Expr := .const (.named "t" ind)
private def u : Expr := .const (.named "u" ind)
private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def v : SVar := ⟨⟨"P", 0⟩, prop⟩
private def predicate : Expr := .const (.named "F" (ind >> prop))
private def body : Expr := .app predicate (.var x)
private def atT : Expr := .app predicate t
private def atU : Expr := .app predicate u
private def context : SubstContext := ⟨[x], body⟩
private def replacement : SubstRule := ⟨[(⟨t, u⟩, [])], context⟩
private def step (pre post : List Expr) (rule : Rule) : Step := ⟨⟨pre, post⟩, rule⟩
private def hyp (φ : Expr) : Step := step [φ] [φ] (.hypothesis φ)
private def identity : LinearProof := #[hyp a, step [] [imp a a] (.rightImp 0 a a)]

private def accepted (name : String) (proof : LinearProof) : IO Unit := do
  match check (leq := CheckerModel.leq) proof with
  | .error e => throw (IO.userError s!"{name}: unexpected rejection: {repr e}")
  | .ok _ => pure ()

private def rejected (name : String) (proof : LinearProof) (expected : CheckError) : IO Unit := do
  match check (leq := CheckerModel.leq) proof with
  | .error e =>
    unless e = expected do
      throw (IO.userError s!"{name}: expected {repr expected}, got {repr e}")
  | .ok _ => throw (IO.userError s!"{name}: accepted invalid proof")

-- Cover every ordinary rule and both import rules.
#eval show IO Unit from do
  accepted "hypothesis" #[hyp a]
  accepted "restate" #[hyp a, step [] [imp a a] (.restate 0)]
  accepted "restateTrue" #[step [] [top] .restateTrue]
  accepted "weakening" #[hyp a, step [a, b] [a, c] (.weakening 0)]
  accepted "cut" #[hyp a, hyp a, step [a] [a] (.cut 0 1 a)]
  accepted "leftAnd" #[hyp a, step [and a b] [a] (.leftAnd 0 a b)]
  accepted "leftOr" #[hyp a, hyp b, hyp c,
    step [or (or a b) c] [a, b, c] (.leftOr [(0, a), (1, b), (2, c)])]
  accepted "leftImp" #[hyp a, hyp b, step [a, imp a b] [b] (.leftImp 0 1 a b)]
  accepted "leftIff" #[hyp (imp a b), step [iff a b] [imp a b] (.leftIff 0 a b)]
  accepted "leftNot" #[hyp a, step [a, neg a] [] (.leftNot 0 a)]
  accepted "leftForall" #[hyp atT, step [forall_ x body] [atT] (.leftForall 0 x body t)]
  accepted "leftExists" #[hyp a, step [exists_ x a] [a] (.leftExists 0 x a)]
  accepted "rightAnd" #[hyp a, hyp b, hyp c,
    step [a, b, c] [and (and a b) c] (.rightAnd [(0, a), (1, b), (2, c)])]
  accepted "rightOr" #[hyp a, step [a] [or a b] (.rightOr 0 a b)]
  accepted "rightImp" identity
  accepted "rightIff" (identity.push (step [] [iff a a] (.rightIff 1 1 a a)))
  accepted "rightNot" #[hyp a, step [] [a, neg a] (.rightNot 0 a)]
  accepted "rightForall" #[hyp a, step [a] [forall_ x a] (.rightForall 0 x a)]
  accepted "rightExists" #[hyp atT, step [atT] [exists_ x body] (.rightExists 0 x body t)]
  accepted "rightEpsilon" #[hyp atT,
    step [atT] [substOne x (epsilon_ (.lam x body)) body] (.rightEpsilon 0 x body t)]
  accepted "leftRefl" #[hyp (eq t t), step [] [eq t t] (.leftRefl 0 t t)]
  accepted "rightRefl" #[step [] [eq t t] (.rightRefl t t)]
  accepted "leftSubst" #[hyp atT, hyp (eq t u),
    step [eq t u, atU] [atT] (.leftSubst 0 1 replacement)]
  accepted "rightSubst" #[hyp atT, hyp (eq t u),
    step [atT, eq t u] [atU] (.rightSubst 0 1 replacement)]
  accepted "instSchema" #[hyp (.var v), step [a] [a] (.instSchema 0 (.cons v a .nil))]
  accepted "singleton leftOr" #[hyp a, step [a] [a] (.leftOr [(0, a)])]
  accepted "duplicate rightAnd" #[hyp a, step [a] [and a a] (.rightAnd [(0, a), (0, a)])]
  accepted "alternate association" #[hyp a, hyp b, hyp c,
    step [or a (or b c)] [a, b, c] (.leftOr [(0, a), (1, b), (2, c)])]
  accepted "assume" #[step [a] [b] .assume]
  accepted "discharge" #[step [a] [a] .assume, hyp a, step [a] [a] (.discharge 0 1)]
  match checkClosed (leq := CheckerModel.leq) identity ⟨[], [imp a a]⟩ with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"closed identity rejected: {repr e}")
  match checkClosed (leq := CheckerModel.leq) identity ⟨[a], [a]⟩ with
  | .error .wrongConclusion => pure ()
  | _ => throw (IO.userError "wrong requested conclusion accepted")

#eval show IO Unit from do
  rejected "empty" #[] .emptyProof
  rejected "self reference" #[step [a] [a] (.restate 0)] (.atStep 0 (.invalidReference 0))
  rejected "forward reference" #[step [a] [a] (.restate 1), hyp a] (.atStep 0 (.invalidReference 1))
  rejected "out of range" #[hyp a, step [a] [a] (.cut 0 100 a)] (.atStep 1 (.invalidReference 100))
  rejected "invalid import" #[step [a] [a] (.restate (-1))] (.atStep 0 (.invalidReference (-1)))
  rejected "n-ary reference" #[hyp a, step [a] [a] (.leftOr [(0, a), (2, a)])]
    (.atStep 1 (.invalidReference 2))
  rejected "ill-sorted conclusion" #[hyp t] (.atStep 0 .illSortedConclusion)
  rejected "ill-sorted witness" #[step [a] [a] (.hypothesis t)] (.atStep 0 .invalidConditions)
  rejected "missing hypothesis" #[step [a] [b] (.hypothesis a)] (.atStep 0 .invalidConditions)
  rejected "unrelated deletion" #[hyp c, step [and a b] [c] (.leftAnd 0 a b)]
    (.atStep 1 .invalidConditions)
  rejected "lost context" #[hyp a, step [and a b] [] (.leftAnd 0 a b)] (.atStep 1 .invalidConditions)
  rejected "missing connective" #[hyp a, step [a] [a] (.leftAnd 0 a b)] (.atStep 1 .invalidConditions)
  rejected "restate reverse direction" #[hyp a, step [] [a] (.restate 0)] (.atStep 1 .invalidConditions)
  rejected "empty leftOr" #[step [bot] [] (.leftOr [])] (.atStep 0 .invalidConditions)
  rejected "empty rightAnd" #[step [] [top] (.rightAnd [])] (.atStep 0 .invalidConditions)
  rejected "ill-sorted annotation" #[hyp a, step [a] [a] (.leftOr [(0, t)])]
    (.atStep 1 .invalidConditions)
  rejected "leftExists eigenvariable" #[hyp body, step [exists_ x body] [body] (.leftExists 0 x body)]
    (.atStep 1 .invalidConditions)
  rejected "rightForall eigenvariable" #[hyp body, step [body] [forall_ x body] (.rightForall 0 x body)]
    (.atStep 1 .invalidConditions)
  rejected "non-term instantiation" #[hyp a, step [a] [exists_ x a] (.rightExists 0 x a b)]
    (.atStep 1 .invalidConditions)
  rejected "missing substitution equality" #[hyp atT, hyp a,
    step [atT, a] [atU] (.rightSubst 0 1 replacement)] (.atStep 2 .invalidConditions)
  rejected "wrong substitution arity" #[hyp atT, step [] [top] .restateTrue,
    step [atT] [atT] (.rightSubst 0 1 ⟨[], context⟩)] (.atStep 2 .invalidConditions)
  rejected "ill-sorted schema" #[hyp (.var v), step [a] [a] (.instSchema 0 (.cons v t .nil))]
    (.atStep 1 .invalidConditions)
  rejected "unused invalid step" #[hyp a, step [a] [b] (.hypothesis a), hyp a]
    (.atStep 1 .invalidConditions)
  rejected "wrong discharge target" #[hyp a, hyp b, step [] [b] (.discharge 0 1)]
    (.atStep 2 .invalidConditions)
  accepted "retained context permits relation equivalence"
    #[hyp a, step [and a b] [and a a] (.leftAnd 0 a b)]
  rejected "schema cannot delete its instantiated context"
    #[hyp a, step [] [top] (.instSchema 0 .nil)] (.atStep 1 .invalidConditions)

-- Discharge removes every equivalent assumption and keeps the premise's actual conclusion.
#eval show IO Unit from do
  let proof := #[step [a] [a] .assume, step [] [imp a a] .assume,
    step [a] [a, imp a a] (.cut 0 1 a), hyp a,
    step [] [top] (.discharge 2 3)]
  match check (leq := CheckerModel.leq) proof with
  | .error e => throw (IO.userError s!"equivalent discharge rejected: {repr e}")
  | .ok result =>
    unless result.assumptions = ∅ do throw (IO.userError "equivalent assumption survived discharge")
    unless result.statement = ⟨[a], [a, imp a a]⟩ do
      throw (IO.userError "discharge replaced actual conclusion with declared metadata")
  let cyclic := #[step [a] [b] .assume, step [a] [b] .assume,
    step [a] [b] (.discharge 0 1)]
  match checkClosed (leq := CheckerModel.leq) cyclic ⟨[a], [b]⟩ with
  | .error .unresolvedAssumptions => pure ()
  | _ => throw (IO.userError "cyclic discharge closed an assumption")
  let imported := #[step [a] [a] (.restate (-1))]
  match check (leq := CheckerModel.leq) imported #[⟨[a], [a]⟩] with
  | .ok result =>
    unless result.assumptions.card = 1 do throw (IO.userError "external import was silently trusted")
  | .error e => throw (IO.userError s!"external import rejected: {repr e}")
  let schema := #[step [Expr.var v] [Expr.var v] .assume,
    step [a] [a] (.instSchema 0 (.cons v a .nil))]
  match check (leq := CheckerModel.leq) schema with
  | .ok result =>
    unless result.assumptions = {⟨[Expr.var v], [Expr.var v]⟩} do
      throw (IO.userError "schema instantiation rewrote recorded dependencies")
  | .error e => throw (IO.userError s!"schema import rejected: {repr e}")
  let duplicated := #[step [a] [a] .assume, hyp a,
    step [a] [and a a] (.rightAnd [(0, a), (1, a)])]
  match check (leq := CheckerModel.leq) duplicated with
  | .ok result =>
    unless result.assumptions = {⟨[a], [a]⟩} do
      throw (IO.userError "n-ary premises conflated distinct dependency sets")
  | .error e => throw (IO.userError s!"n-ary dependency union rejected: {repr e}")

example {Γ Δ ss} (imports : ∀ s ∈ ss,
    Nonempty (Weakened.ProofTree CheckerModel.leq s.1 s.2)) :
    Nonempty (Imported.ProofTree CheckerModel.leq Γ Δ ss) ↔
      Nonempty (Weakened.ProofTree CheckerModel.leq Γ Δ) :=
  Imported.withAssumptions_iff imports

#print axioms Imported.resolve
#print axioms Imported.withAssumptions_iff
#print axioms Imported.Checker.check
#print axioms Imported.Checker.checkClosed
