import Lisa.Combined

namespace Lisa.Tests.Combined

open Expr Orthologic Imported Imported.Checker

private def a : Expr := .const (.named "A" prop)
private def b : Expr := .const (.named "B" prop)
private def c : Expr := .const (.named "C" prop)
private def x : SVar := ⟨⟨"x", 0⟩, prop⟩
private def y : SVar := ⟨⟨"y", 0⟩, prop⟩
private def ix : SVar := ⟨⟨"x", 0⟩, ind⟩
private def iy : SVar := ⟨⟨"y", 0⟩, ind⟩
private def betaA : Expr := .app (.lam x (.var x)) a
private def observe : Expr := .const (.named "observe" ((prop >> prop) >> prop))
private def opaqueFn : Expr := .const (.named "opaque" (prop >> prop))
private def pred : Expr := .const (.named "P" (ind >> prop))
private def otherPred : Expr := .const (.named "Q" (ind >> prop))
private def check := Lisa.Combined.check
private def replay := Lisa.Combined.Replay.check

-- A single contextual budget must not charge outer propositional wrappers.
#guard check 0 betaA a
#guard check 0 (or betaA betaA) a
#guard check 0 (and betaA (neg a)) bot
#guard check 0 top (or betaA (neg a))
#guard check 0 (.app (.lam x (and (.var x) b)) a) (and a b)

-- The ordered-atom extension shares normalization and supplies the same checker interfaces.
#guard Lisa.Combined.Ordered.check (Eq : ExprRel) 0 betaA a
#guard Lisa.Combined.Ordered.check (Eq : ExprRel) 0 (or betaA betaA) a
#guard !Lisa.Combined.Ordered.check (Eq : ExprRel) 0 a b

example (r : ExprRel) [DecidableRel r] [IsPreorder Expr r] (budget : Nat)
    (proof : LinearProof) (target : Statement) :
    Except CheckError (ClosedChecked (Lisa.Combined.Ordered.leq r budget) target) :=
  Imported.Checker.checkClosed proof target

example (r : ExprRel) [DecidableRel r] [IsPreorder Expr r]
    (hsound : ∀ {p q}, r p q → ExpressionOrder.leq p q) (budget : Nat) :
    letI : OrderReduction ExpressionOrder.leq := Orthologic.reduction ExpressionOrder.leq ExpressionOrder.interpretation
    Subrelation (Lisa.Combined.Ordered.leq r budget) ExpressionOrder.leq :=
  Lisa.Combined.Ordered.simulation r hsound budget

example (r : ExprRel) [DecidableRel r] [IsPreorder Expr r]
    (hsound : ∀ {p q}, r p q → ExpressionOrder.leq p q)
    {budget : Nat} {target : Statement}
    (result : ClosedChecked (Lisa.Combined.Ordered.leq r budget) target) :
    Nonempty (Lisa.Combined.ReferenceProof target) :=
  Lisa.Combined.Ordered.certificate_sound r hsound result

-- Normalize beneath opaque constructors without assuming their monotonicity.
#guard check 8 (.app observe (.lam x (and (.var x) top)))
  (.app observe (.lam y (.var y)))
#guard check 8 (.app opaqueFn (and a top)) (.app opaqueFn a)
#guard !check 8 (.app opaqueFn (and a b)) (.app opaqueFn a)
#guard !check 8 (and a (or b c)) (or (and a b) (and a c))

-- Preserve capture avoidance, free-variable identities and malformed-sort boundaries.
private def capture : Expr := .app (.lam ix (.lam iy (.var ix))) (.var iy)
private def badBeta : Expr := .app (.lam ix (.var ix)) a

#guard check 4 capture (.lam ⟨⟨"z", 0⟩, ind⟩ (.var iy))
#guard !check 4 capture (.lam iy (.var iy))
#guard !check 4 (.var ix) (.var iy)
#guard !check 4 badBeta a
#guard !check 4 (.app (.const (.named "not" (ind >> prop))) (.var ix)) (neg (.var ix))
#guard check 4 (eq (.var ix) (.var ix)) top
#guard !check 4 top (eq (.var ix) (.var iy))
#guard check 0 (eq (.var ix) (.var iy)) (eq (.var iy) (.var ix))
#guard check 0 (eq (.var iy) (.var ix)) (eq (.var ix) (.var iy))
#guard check 8 (.app opaqueFn (eq (.var ix) (.var iy)))
  (.app opaqueFn (eq (.var iy) (.var ix)))
#guard check 8 (.app observe (.lam x (eq (.var ix) (.var iy))))
  (.app observe (.lam y (eq (.var iy) (.var ix))))
#guard !check 8 (eq (.var ix) (.var ix)) (eq (.var ix) (.var iy))

-- Atomic inequalities are not yet supplied by the independent-atom backend.
private def narrow : Expr := forall_ ix (and a b)
private def wide : Expr := forall_ iy a

example : ExpressionOrder.leq narrow wide := by
  exact .trans (.forallMono ix rfl (by decide) (by decide) (.meetLeft _ _))
    (.alphaBetaEta (.alpha (by decide)))
#guard !check 8 narrow wide
#guard !check 8 (and narrow (neg wide)) bot

-- PRO005+2 step 298 needs monotonicity of the quantified body, not constructor congruence.
#guard !check 8 (forall_ ix (iff a b)) (forall_ ix (imp b a))
example : ExpressionOrder.leq (forall_ ix (iff a b)) (forall_ ix (imp b a)) :=
  .forallMono ix rfl (by decide) (by decide)
    (.trans (.iff a b) (.meetRight _ _))

-- Quantified inequalities must survive the outer OL shell and reverse under negation.
#guard replay 8 narrow wide
#guard replay 8 (and narrow (neg wide)) bot
#guard replay 8 top (or (neg narrow) wide)
#guard replay 8 (neg wide) (neg narrow)
#guard !replay 8 wide narrow
#guard !replay 8 (neg narrow) (neg wide)
#guard replay 8 (forall_ ix (iff a b)) (forall_ iy (imp a b))
#guard replay 8 (forall_ ix (iff a b)) (forall_ iy (imp b a))
#guard !replay 8 (forall_ ix (imp a b)) (forall_ iy (iff a b))
#guard replay 8 (forall_ ix (and (forall_ iy (and a b)) c))
  (forall_ ix (and (forall_ iy a) c))
#guard !replay 8 (forall_ ix (and (forall_ iy a) c))
  (forall_ ix (and (forall_ iy (and a b)) c))

-- Congruence of an opaque function must not turn a strict body inequality into equality.
#guard !replay 8 (.app opaqueFn narrow) (.app opaqueFn wide)
#guard !replay 8 (.app opaqueFn (and a b)) (.app opaqueFn a)
#guard !replay 8 (and a (or b c)) (or (and a b) (and a c))
#guard !replay 8 (forall_ ix (.app pred (.var iy))) (forall_ iy (.app pred (.var iy)))
#guard !replay 8 (forall_ x a) (forall_ x b)
#guard !replay 8 badBeta a
#guard replay 8 (forall_ ix (and (.app pred (.var ix)) (.app otherPred (.var ix))))
  (forall_ iy (.app pred (.var iy)))
#guard !replay 8 (forall_ iy (.app pred (.var iy)))
  (forall_ ix (and (.app pred (.var ix)) (.app otherPred (.var ix))))
#guard check 0 (.app observe (.lam x (and (.var x) top)))
  (.app observe (.lam y (.var y)))

-- Constructor congruence sees commutativity even below several binders.
#guard check 0 (.app opaqueFn (and a b)) (.app opaqueFn (and b a))
#guard check 0 (forall_ ix (forall_ iy (and a b)))
  (forall_ ix (forall_ iy (and b a)))
#guard !check 0 (.app opaqueFn (and a b)) (.app opaqueFn (or a b))

-- Existential expansion introduces a fresh binder; re-canonicalize it before comparison.
#guard check 8 (neg (exists_ ix (imp a (.app pred (.var ix)))))
  (forall_ iy (and a (neg (.app pred (.var iy)))))
#guard check 8 (forall_ iy (and a (neg (.app pred (.var iy)))))
  (neg (exists_ ix (imp a (.app pred (.var ix)))))
#guard !check 8 (neg (exists_ ix (imp a (.app pred (.var ix)))))
  (forall_ iy (and b (neg (.app pred (.var iy)))))

private def allNested : Nat → Expr → Expr
  | 0, p => p
  | n + 1, p => forall_ ix (allNested n p)

private def existsNested : Nat → Expr → Expr
  | 0, p => p
  | n + 1, p => exists_ iy (existsNested n p)

-- Builtin desugaring is independent of the contextual OL simplification budget.
#guard check 0 (existsNested 10 a) (neg (allNested 10 (neg a)))
#guard check 0 (neg (allNested 10 (imp a b))) (existsNested 10 (and a (neg b)))
#guard replay 8 (neg (allNested 4 (imp a b))) (existsNested 4 (and a (neg b)))
#guard replay 8 (existsNested 4 (and a (neg b))) (neg (allNested 4 (imp a b)))
#guard replay 8 (allNested 4 (iff a b)) (allNested 4 (imp b a))
#guard !replay 8 (allNested 4 (imp b a)) (allNested 4 (iff a b))
#guard check 0 (eq (.var ix) (.var ix)) top

example {budget : Nat} {p q : Expr} (h : Lisa.Combined.leq budget p q) :
    ExpressionOrder.leq p q := Lisa.Combined.sound h

example {budget : Nat} {target : Statement}
    (result : ClosedChecked (Lisa.Combined.Replay.leq budget) target) :
    Nonempty (Lisa.Combined.ReferenceProof target) :=
  Lisa.Combined.certificate_sound result

private def step (pre post : List Expr) (rule : Rule) : Step := ⟨⟨pre, post⟩, rule⟩
private def hyp (p : Expr) := step [p] [p] (.hypothesis p)

private def accepted (name : String) (proof : LinearProof) (target : Statement) : IO Unit := do
  match Lisa.Combined.checkClosed 8 proof target with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"{name}: {repr e}")

private def rejected (name : String) (proof : LinearProof) (expected : CheckError) : IO Unit := do
  match Lisa.Combined.checkProof 8 proof with
  | .error e =>
    unless e = expected do throw (IO.userError s!"{name}: {repr e}")
  | .ok _ => throw (IO.userError s!"{name}: accepted invalid proof")

#eval show IO Unit from do
  accepted "identity" #[hyp a, step [] [imp a a] (.rightImp 0 a a)] ⟨[], [imp a a]⟩
  accepted "beta restatement" #[hyp a, step [betaA] [a] (.restate 0)] ⟨[betaA], [a]⟩
  accepted "discharge" #[step [betaA] [a] .assume, hyp a,
    step [betaA] [a] (.discharge 0 1)] ⟨[betaA], [a]⟩
  accepted "permuted duplicated encoding" #[
    step [a, b, a] [a, b] .assume, step [b, a] [b, a, a] (.hypothesis a),
    step [a, b] [a, b] (.discharge 0 1)] ⟨[b, a], [b, a]⟩
  accepted "truth" #[step [] [top] .restateTrue] ⟨[], [top]⟩
  let contradiction := and narrow (neg wide)
  let richHyp := step [contradiction] [bot] (.hypothesis bot)
  match checkStepMatching (Lisa.Combined.Replay.matching 8) #[] #[] richHyp with
  | .error .invalidConditions => pure ()
  | _ => throw (IO.userError "Cheap matcher no longer isolates the quantified fallback")
  accepted "rich matching fallback" #[richHyp] ⟨[contradiction], [bot]⟩
  rejected "invalid matching fallback"
    #[step [and a (neg b)] [bot] (.hypothesis bot)] (.atStep 0 .invalidConditions)
  rejected "self reference" #[step [a] [a] (.restate 0)] (.atStep 0 (.invalidReference 0))
  rejected "forward reference" #[step [a] [a] (.restate 1), hyp a] (.atStep 0 (.invalidReference 1))
  rejected "bad import" #[step [a] [a] (.restate (-1))] (.atStep 0 (.invalidReference (-1)))
  rejected "ill-sorted beta" #[hyp badBeta] (.atStep 0 .illSortedConclusion)
  accepted "quantified comparison"
    #[hyp narrow, step [narrow] [wide] (.weakening 0)] ⟨[narrow], [wide]⟩
  accepted "quantified iff weakening"
    #[hyp (forall_ ix (iff a b)),
      step [forall_ ix (iff a b)] [forall_ ix (imp b a)] (.weakening 0)]
    ⟨[forall_ ix (iff a b)], [forall_ ix (imp b a)]⟩
  rejected "reversed quantified weakening"
    #[hyp (forall_ ix (imp b a)),
      step [forall_ ix (imp b a)] [forall_ ix (iff a b)] (.weakening 0)]
    (.atStep 1 .invalidConditions)
  let cyclic := #[step [a] [b] .assume, step [a] [b] .assume,
    step [a] [b] (.discharge 0 1)]
  match Lisa.Combined.checkClosed 8 cyclic ⟨[a], [b]⟩ with
  | .error .unresolvedAssumptions => pure ()
  | _ => throw (IO.userError "cyclic discharge closed an assumption")
  match Lisa.Combined.checkProof 8 #[step [a] [a] (.restate (-1))] #[⟨[a], [a]⟩] with
  | .ok result =>
    unless result.assumptions.card = 1 do throw (IO.userError "external import was trusted")
  | .error e => throw (IO.userError s!"external import rejected: {repr e}")

-- Check encoding invariance across all pairs of empty, duplicate and permuted sequents.
#eval show IO Unit from do
  let samples : List Statement :=
    [⟨[], []⟩, ⟨[], [top]⟩, ⟨[], [a, b, a]⟩, ⟨[], [b, a]⟩,
      ⟨[a, betaA, a], [a, b]⟩, ⟨[b, a], [b, a, a]⟩, ⟨[a, a], []⟩, ⟨[a], []⟩]
  for s in samples do
    for t in samples do
      letI := Statement.decideLeq (leq := Lisa.Combined.leq 2) s t
      unless decide (sequentLeq (Lisa.Combined.leq 2)
          s.sequent.1 s.sequent.2 t.sequent.1 t.sequent.2) =
          check 2 s.formula t.formula do
        throw (IO.userError "combined encoding changed a comparison")

-- Compare prepared context decisions with their original pointwise definitions.
#eval show IO Unit from do
  let contexts := ([[], [a], [b], [a, b, a], [and a top], [and a a],
    [betaA, badBeta], [narrow, a]] : List (List Expr)).map List.toFinset
  for Γ in contexts do
    for Δ in contexts do
      let originalSubset := decide (∀ p ∈ Γ, ∃ q ∈ Δ,
        OrderReduction.reduce (leq := Lisa.Combined.Replay.leq 8) p =
          OrderReduction.reduce (leq := Lisa.Combined.Replay.leq 8) q)
      unless decide (reducedSubset (Lisa.Combined.Replay.leq 8) Γ Δ) = originalSubset do
        throw (IO.userError "Prepared context changed reduced inclusion")
      for principal in [a, b, betaA] do
        let originalExcept := decide (∀ p ∈ Γ,
          (∃ q ∈ Δ, isSame (Lisa.Combined.Replay.leq 8) p q) ∨
          isSame (Lisa.Combined.Replay.leq 8) p principal)
        unless decide (containedExcept (Lisa.Combined.Replay.leq 8) Γ Δ principal) =
            originalExcept do
          throw (IO.userError "Prepared context changed the principal exception")

#print axioms Lisa.Combined.sound
#print axioms Lisa.Combined.Quantified.sound
#print axioms Lisa.Combined.Replay.sound
#print axioms Lisa.Combined.Replay.check_iff
#print axioms Imported.Checker.checkStepMatching
#print axioms Imported.Checker.checkStepFallback
#print axioms Imported.Checker.checkStepFallback_exact
#print axioms Lisa.Orthologic.QuantifiedProjection.lift
#print axioms Lisa.Combined.check_eq_contextual
#print axioms Lisa.Combined.certificate_sound
#print axioms Lisa.Combined.Ordered.certificate_sound
#print axioms Imported.resolveWith
#print axioms ClosedChecked.resolveWith

end Lisa.Tests.Combined
