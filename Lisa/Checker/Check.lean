import Lisa.Checker.Data
import Lisa.ImportedWeakened

open Lisa Expr

namespace Imported.Checker

inductive Rule where
  | assume
  | discharge (premise justification : Int)
  | restate (premise0 : Int)
  | weakening (premise0 : Int)
  | restateTrue
  | hypothesis (α : Expr)
  | cut (premise0 : Int) (premise1 : Int) (α : Expr)
  | leftAnd (premise0 : Int) (α : Expr) (β : Expr)
  | leftOr (premises : List (Int × Expr))
  | leftImp (premise0 : Int) (premise1 : Int) (α : Expr) (β : Expr)
  | leftIff (premise0 : Int) (α : Expr) (β : Expr)
  | leftNot (premise0 : Int) (α : Expr)
  | leftForall (premise0 : Int) (x : SVar) (α : Expr) (t : Expr)
  | leftExists (premise0 : Int) (x : SVar) (α : Expr)
  | rightAnd (premises : List (Int × Expr))
  | rightOr (premise0 : Int) (α : Expr) (β : Expr)
  | rightImp (premise0 : Int) (α : Expr) (β : Expr)
  | rightIff (premise0 : Int) (premise1 : Int) (α : Expr) (β : Expr)
  | rightNot (premise0 : Int) (α : Expr)
  | rightForall (premise0 : Int) (x : SVar) (α : Expr)
  | rightExists (premise0 : Int) (x : SVar) (α : Expr) (t : Expr)
  | rightEpsilon (premise0 : Int) (x : SVar) (α : Expr) (t : Expr)
  | leftRefl (premise0 : Int) (s : Expr) (t : Expr)
  | rightRefl (s : Expr) (t : Expr)
  | leftSubst (premise comparison : Int) (replacement : SubstRule)
  | rightSubst (premise comparison : Int) (replacement : SubstRule)
  | instSchema (premise0 : Int) (σ : Subst)

/-- Name a rule without rendering its expression parameters. -/
def Rule.name : Rule → String
  | .assume => "assume"
  | .discharge .. => "discharge"
  | .restate .. => "restate"
  | .weakening .. => "weakening"
  | .restateTrue => "restateTrue"
  | .hypothesis .. => "hypothesis"
  | .cut .. => "cut"
  | .leftAnd .. => "leftAnd"
  | .leftOr .. => "leftOr"
  | .leftImp .. => "leftImp"
  | .leftIff .. => "leftIff"
  | .leftNot .. => "leftNot"
  | .leftForall .. => "leftForall"
  | .leftExists .. => "leftExists"
  | .rightAnd .. => "rightAnd"
  | .rightOr .. => "rightOr"
  | .rightImp .. => "rightImp"
  | .rightIff .. => "rightIff"
  | .rightNot .. => "rightNot"
  | .rightForall .. => "rightForall"
  | .rightExists .. => "rightExists"
  | .rightEpsilon .. => "rightEpsilon"
  | .leftRefl .. => "leftRefl"
  | .rightRefl .. => "rightRefl"
  | .leftSubst .. => "leftSubst"
  | .rightSubst .. => "rightSubst"
  | .instSchema .. => "instSchema"

/-- List the proof references used by a rule. -/
def Rule.references : Rule → List Int
  | .assume | .restateTrue | .hypothesis .. | .rightRefl .. => []
  | .discharge i j | .cut i j _ | .leftImp i j .. | .rightIff i j .. => [i, j]
  | .leftSubst i j _ | .rightSubst i j _ => [i, j]
  | .leftOr ps | .rightAnd ps => ps.map Prod.fst
  | .restate i | .weakening i | .leftAnd i .. | .leftIff i ..
  | .leftNot i .. | .leftForall i .. | .leftExists i .. | .rightOr i ..
  | .rightImp i .. | .rightNot i .. | .rightForall i .. | .rightExists i ..
  | .rightEpsilon i .. | .leftRefl i .. | .instSchema i .. => [i]

structure Step where
  statement : Statement
  rule : Rule

abbrev LinearProof := Array Step

section Checking

local notation "leq" => ProofRelation

/-- Resolve only checked earlier steps or declared external imports. -/
def lookup (imports checked : Array (Checked leq)) (reference : Int) :
    Except CheckError (Checked leq) :=
  if reference < 0 then
    match imports[(-reference - 1).toNat]? with
    | some p => .ok p
    | none => .error (.invalidReference reference)
  else
    match checked[reference.toNat]? with
    | some p => .ok p
    | none => .error (.invalidReference reference)

private def annotated (p : Checked leq × Expr) : Premise :=
  ⟨p.1.statement.sequent.1, p.1.statement.sequent.2,
    p.2, p.1.assumptions.image Statement.sequent⟩

private def dependencies (ps : List (Checked leq × Expr)) : Finset Statement :=
  ps.foldr (fun p acc => p.1.assumptions ∪ acc) ∅

private theorem image_dependencies (ps : List (Checked leq × Expr)) :
    (dependencies ps).image Statement.sequent =
      premiseAssumptions (ps.map annotated) := by
  induction ps with
  | nil => simp [dependencies, premiseAssumptions]
  | cons p ps ih =>
    simpa only [dependencies, List.foldr_cons, Finset.image_union,
      List.map_cons, premiseAssumptions, annotated] using congrArg
      (fun ss => p.1.assumptions.image Statement.sequent ∪ ss) ih

/-- Check every match using the single certified LambdaFOL OL interface. -/
def checkStep (imports checked : Array (Checked leq)) (step : Step) :
    Except CheckError (Checked leq) := do
  let output := step.statement
  let Ω₁ := output.sequent.1
  let Ω₂ := output.sequent.2
  if hsort : isFSet Ω₁ ∧ isFSet Ω₂ then
    match step.rule with
    | .assume => do
      return ⟨output, {output}, by
        simpa using (show Nonempty (ProofTree leq Ω₁ Ω₂ {(Ω₁, Ω₂)}) from
          ⟨.assume hsort.1 hsort.2⟩)⟩
    | .discharge premise justification => do
      let p0 ← lookup imports checked premise
      let p1 ← lookup imports checked justification
      letI : Testable _ := ⟨Statement.testSame p0.statement output⟩
      let condition := verify (sameSequent leq p0.statement.sequent output.sequent)
      if heq : condition.ok then
        have heq := condition.sound heq
        let remaining := p0.assumptions.filter fun s =>
          (Statement.testSame s p1.statement).ok ≠ true
        return ⟨p0.statement, remaining ∪ p1.assumptions, by
          classical
          let d := ProofTree.discharge (Classical.choice p0.certificate) (Classical.choice p1.certificate)
          apply Nonempty.intro (d.weakenAssumptions ?_ ?_)
          · intro s hs
            rcases Finset.mem_union.mp hs with hs | hs
            · obtain ⟨hs, hn⟩ := Finset.mem_filter.mp hs
              obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
              exact Finset.mem_image.mpr ⟨t, Finset.mem_union_left _ (Finset.mem_filter.mpr
                ⟨ht, fun h => hn ((Statement.testSame t p1.statement).sound h)⟩), rfl⟩
            · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
              exact Finset.mem_image.mpr ⟨t, Finset.mem_union_right _ ht, rfl⟩
          · intro s hs
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
            rcases Finset.mem_union.mp ht with ht | ht
            · exact assumptionsWellSorted (Classical.choice p0.certificate) _
                (Finset.mem_image.mpr ⟨t, (Finset.mem_filter.mp ht).1, rfl⟩)
            · exact assumptionsWellSorted (Classical.choice p1.certificate) _
                (Finset.mem_image.mpr ⟨t, ht, rfl⟩)⟩
      else throw .invalidConditions
    | .restate premise0 => do
      let p0 ← lookup imports checked premise0
      let condition := Statement.testSame p0.statement output
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, _⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.weakening hsort.1 hsort.2 tree0 h5⟩⟩
      else throw .invalidConditions
    | .weakening premise0 => do
      let p0 ← lookup imports checked premise0
      letI : Testable _ := ⟨Statement.testLeq p0.statement output⟩
      let condition := verify ((sequentLeq leq p0.statement.sequent.1 p0.statement.sequent.2 Ω₁ Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          let tree0 := Classical.choice p0.certificate
          exact ⟨.weakening hsort.1 hsort.2 tree0 h⟩⟩
      else throw .invalidConditions
    | .restateTrue => do
      letI : Testable _ := ⟨Statement.testTrue output⟩
      let condition := verify ((isSame leq (sequentToFormula Ω₁ Ω₂) top))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, ∅, by
          classical
          exact ⟨.restateTrue hsort.1 hsort.2 h⟩⟩
      else throw .invalidConditions
    | .hypothesis α => do
      let condition := verify ((isFormula α) ∧
          (ordContains leq α Ω₁) ∧
          (ordContains leq α Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, ∅, by
          classical
          rcases h with ⟨h2, h3, h4⟩
          exact ⟨.hypothesis α
            hsort.1 hsort.2 h2
            h3 h4⟩⟩
      else throw .invalidConditions
    | .cut premise0 premise1 α => do
      let p0 ← lookup imports checked premise0
      let p1 ← lookup imports checked premise1
      let condition := verify ((isFormula α) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (setLeq leq p1.statement.sequent.2 Ω₂) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ (α)) ∧
          (containedExcept leq p1.statement.sequent.1 Ω₁ (α)))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨h8, h9, h10, h11, h12⟩
          let tree0 := Classical.choice p0.certificate
          let tree1 := Classical.choice p1.certificate
          rw [Finset.image_union]
          exact ⟨.cut α tree0 tree1
            hsort.1 hsort.2 h8 h9 h10
            h11 h12⟩⟩
      else throw .invalidConditions
    | .leftAnd premise0 α β => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExceptEither leq p0.statement.sequent.1 Ω₁ (α) (β)) ∧
          (ordContains leq (and α β) Ω₁))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftAnd α β tree0
            hsort.1 hsort.2 h5 h6 h7
            h8 h9⟩⟩
      else throw .invalidConditions
    | .leftOr references => do
      let ps ← references.mapM fun (ref, φ) => do
        let p ← lookup imports checked ref
        pure (p, φ)
      let prems := ps.map annotated
      let condition := verify (prems ≠ [] ∧
          (∀ prem ∈ prems, isFormula prem.val.1) ∧
          (∀ prem ∈ prems, setLeq leq prem.post Ω₂ ∧
            containedExcept leq prem.pre Ω₁ prem.val.1) ∧
          ordContains leq (foldFormulas or bot (prems.map (fun prem : Premise => prem.val.1))) Ω₁)
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, dependencies ps, by
          classical
          rw [image_dependencies]
          refine ⟨.leftOr h.1 hsort.1 hsort.2 h.2.1 ?_
            (fun prem hp => ⟨(h.2.2.1 prem hp).1, (h.2.2.1 prem hp).2⟩)
            h.2.2.2⟩
          intro prem hp
          let found := List.mem_map.mp hp
          let p := Classical.choose found
          have hp' := (Classical.choose_spec found).1
          have heq := (Classical.choose_spec found).2
          rw [← heq]
          exact Classical.choice p.1.certificate⟩
      else throw .invalidConditions
    | .leftImp premise0 premise1 α β => do
      let p0 ← lookup imports checked premise0
      let p1 ← lookup imports checked premise1
      let condition := verify ((isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (setLeq leq p1.statement.sequent.2 Ω₂) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ (α)) ∧
          (containedExcept leq p1.statement.sequent.1 Ω₁ (β)) ∧
          (ordContains leq (imp α β) Ω₁))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨h8, h9, h10, h11, h12, h13, h14⟩
          let tree0 := Classical.choice p0.certificate
          let tree1 := Classical.choice p1.certificate
          rw [Finset.image_union]
          exact ⟨.leftImp α β tree0 tree1
            hsort.1 hsort.2 h8 h9 h10 h11
            h12 h13 h14⟩⟩
      else throw .invalidConditions
    | .leftIff premise0 α β => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExceptEither leq p0.statement.sequent.1 Ω₁ ((imp α β)) ((imp β α))) ∧
          (ordContains leq (iff α β) Ω₁))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftIff α β tree0
            hsort.1 hsort.2 h5 h6 h7
            h8 h9⟩⟩
      else throw .invalidConditions
    | .leftNot premise0 α => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((isFormula α) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ (α)) ∧
          (ordContains leq (neg α) Ω₁))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftNot α tree0
            hsort.1 hsort.2 h5 h6
            h7 h8⟩⟩
      else throw .invalidConditions
    | .leftForall premise0 x α t => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((x.sort = ind) ∧
          (isFormula α) ∧
          (isTerm t) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept leq p0.statement.sequent.1 Ω₁ ((substOne x t α))) ∧
          (ordContains leq (forall_ x α) Ω₁))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftForall x α t tree0
            hsort.1 hsort.2 h5 h6 h7 h8
            h9 h10⟩⟩
      else throw .invalidConditions
    | .leftExists premise0 x α => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((x.sort = ind) ∧
          (isFormula α) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept leq p0.statement.sequent.1 Ω₁ (α)) ∧
          (ordContains leq (exists_ x α) Ω₁) ∧
          (x ∉ freeVars (Ω₁ ∪ Ω₂)))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftExists x α tree0
            hsort.1 hsort.2 h5 h6 h7
            h8 h9 h10⟩⟩
      else throw .invalidConditions
    | .rightAnd references => do
      let ps ← references.mapM fun (ref, φ) => do
        let p ← lookup imports checked ref
        pure (p, φ)
      let prems := ps.map annotated
      let condition := verify (prems ≠ [] ∧
          (∀ prem ∈ prems, isFormula prem.val.1) ∧
          (∀ prem ∈ prems, setLeq leq prem.pre Ω₁ ∧
            containedExcept leq prem.post Ω₂ prem.val.1) ∧
          ordContains leq (foldFormulas and top (prems.map (fun prem : Premise => prem.val.1))) Ω₂)
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, dependencies ps, by
          classical
          rw [image_dependencies]
          refine ⟨.rightAnd h.1 hsort.1 hsort.2 h.2.1 ?_
            (fun prem hp => ⟨(h.2.2.1 prem hp).1, (h.2.2.1 prem hp).2⟩)
            h.2.2.2⟩
          intro prem hp
          let found := List.mem_map.mp hp
          let p := Classical.choose found
          have hp' := (Classical.choose_spec found).1
          have heq := (Classical.choose_spec found).2
          rw [← heq]
          exact Classical.choice p.1.certificate⟩
      else throw .invalidConditions
    | .rightOr premise0 α β => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExceptEither leq p0.statement.sequent.2 Ω₂ (α) (β)) ∧
          (ordContains leq (or α β) Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightOr α β tree0
            hsort.1 hsort.2 h5 h6 h7
            h8 h9⟩⟩
      else throw .invalidConditions
    | .rightImp premise0 α β => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((isFormula α) ∧
          (isFormula β) ∧
          (containedExcept leq p0.statement.sequent.1 Ω₁ (α)) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ (β)) ∧
          (ordContains leq (imp α β) Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightImp α β tree0
            hsort.1 hsort.2 h5 h6
            h7 h8 h9⟩⟩
      else throw .invalidConditions
    | .rightIff premise0 premise1 α β => do
      let p0 ← lookup imports checked premise0
      let p1 ← lookup imports checked premise1
      let condition := verify ((isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (setLeq leq p1.statement.sequent.1 Ω₁) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ ((imp α β))) ∧
          (containedExcept leq p1.statement.sequent.2 Ω₂ ((imp β α))) ∧
          (ordContains leq (iff α β) Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨h8, h9, h10, h11, h12, h13, h14⟩
          let tree0 := Classical.choice p0.certificate
          let tree1 := Classical.choice p1.certificate
          rw [Finset.image_union]
          exact ⟨.rightIff α β tree0 tree1
            hsort.1 hsort.2 h8 h9 h10 h11
            h12 h13 h14⟩⟩
      else throw .invalidConditions
    | .rightNot premise0 α => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((isFormula α) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept leq p0.statement.sequent.1 Ω₁ (α)) ∧
          (ordContains leq (neg α) Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightNot α tree0
            hsort.1 hsort.2 h5 h6
            h7 h8⟩⟩
      else throw .invalidConditions
    | .rightForall premise0 x α => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((x.sort = ind) ∧
          (isFormula α) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ (α)) ∧
          (ordContains leq (forall_ x α) Ω₂) ∧
          (x ∉ freeVars (Ω₁ ∪ Ω₂)))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightForall x α tree0
            hsort.1 hsort.2 h5 h6 h7
            h8 h9 h10⟩⟩
      else throw .invalidConditions
    | .rightExists premise0 x α t => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((x.sort = ind) ∧
          (isFormula α) ∧
          (isTerm t) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ ((substOne x t α))) ∧
          (ordContains leq (exists_ x α) Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightExists x α t tree0
            hsort.1 hsort.2 h5 h6 h7 h8
            h9 h10⟩⟩
      else throw .invalidConditions
    | .rightEpsilon premise0 x α t => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((x.sort = ind) ∧
          (isFormula α) ∧
          (isTerm t) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept leq p0.statement.sequent.2 Ω₂ ((substOne x t α))) ∧
          (ordContains leq (substOne x (epsilon_ (.lam x α)) α) Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightEpsilon x α t tree0
            hsort.1 hsort.2 h5 h6 h7 h8
            h9 h10⟩⟩
      else throw .invalidConditions
    | .leftRefl premise0 s t => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((isTerm s) ∧
          (isTerm t) ∧
          (isSame leq s t) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept leq p0.statement.sequent.1 Ω₁ ((eq s t))))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftRefl s t tree0
            hsort.1 hsort.2 h5 h6
            h7 h8 h9⟩⟩
      else throw .invalidConditions
    | .rightRefl s t => do
      let condition := verify ((isTerm s) ∧
          (isTerm t) ∧
          (isSame leq s t) ∧
          (ordContains leq (eq s t) Ω₂))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, ∅, by
          classical
          rcases h with ⟨h2, h3, h4, h5⟩
          exact ⟨.rightRefl s t
            hsort.1 hsort.2 h2 h3
            h4 h5⟩⟩
      else throw .invalidConditions
    | .leftSubst premise comparison r => do
      let p0 ← lookup imports checked premise
      let p1 ← lookup imports checked comparison
      let Θ := p1.statement.sequent.1
      let Ξ := p1.statement.sequent.2.erase r.equation
      let condition := verify (r.valid ∧ r.equation ∈ p1.statement.sequent.2 ∧ r.fresh Θ Ξ ∧
          containedExcept leq p0.statement.sequent.1 Ω₁ r.source ∧
          setLeq leq p0.statement.sequent.2 Ω₂ ∧ ordContains leq r.target Ω₁ ∧
          setLeq leq Θ Ω₁ ∧ setLeq leq Ξ Ω₂)
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨hv, he, hf, hl, hr, ha, hΘ, hΞ⟩
          rw [Finset.image_union]
          have comparisonTree : ProofTree leq Θ (insert r.equation Ξ)
              (p1.assumptions.image Statement.sequent) := by
            simpa only [Ξ, Finset.insert_erase he] using Classical.choice p1.certificate
          exact ⟨.leftSubst r (Classical.choice p0.certificate) comparisonTree
            hsort.1 hsort.2 hv hf hl hr ha hΘ hΞ⟩⟩
      else throw .invalidConditions
    | .rightSubst premise comparison r => do
      let p0 ← lookup imports checked premise
      let p1 ← lookup imports checked comparison
      let Θ := p1.statement.sequent.1
      let Ξ := p1.statement.sequent.2.erase r.equation
      let condition := verify (r.valid ∧ r.equation ∈ p1.statement.sequent.2 ∧ r.fresh Θ Ξ ∧
          setLeq leq p0.statement.sequent.1 Ω₁ ∧
          containedExcept leq p0.statement.sequent.2 Ω₂ r.source ∧
          ordContains leq r.target Ω₂ ∧ setLeq leq Θ Ω₁ ∧ setLeq leq Ξ Ω₂)
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨hv, he, hf, hl, hr, ha, hΘ, hΞ⟩
          rw [Finset.image_union]
          have comparisonTree : ProofTree leq Θ (insert r.equation Ξ)
              (p1.assumptions.image Statement.sequent) := by
            simpa only [Ξ, Finset.insert_erase he] using Classical.choice p1.certificate
          exact ⟨.rightSubst r (Classical.choice p0.certificate) comparisonTree
            hsort.1 hsort.2 hv hf hl hr ha hΘ hΞ⟩⟩
      else throw .invalidConditions
    | .instSchema premise0 σ => do
      let p0 ← lookup imports checked premise0
      let condition := verify ((Subst.wellSorted σ) ∧
          ((
        let Γ₁' := p0.statement.sequent.1.image (Subst.subst σ)
        let Γ₂' := p0.statement.sequent.2.image (Subst.subst σ)

        setLeq leq Γ₁' Ω₁ ∧ setLeq leq Γ₂' Ω₂
      )))
      if h : condition.ok then
        have h := condition.sound h
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.instSchema σ tree0
            hsort.1 hsort.2 h5 h6⟩⟩
      else throw .invalidConditions
  else throw .illSortedConclusion

/-- Check every record; return the actual conclusion of the final checked step. -/
def check (proof : LinearProof) (external : Array Statement := #[]) :
    Except CheckError (Checked leq) := do
  let imports ← external.mapM fun statement => checkStep #[] #[] ⟨statement, .assume⟩
  let mut checked := #[]
  for step in proof do
    match checkStep imports checked step with
    | .error e => throw (.atStep checked.size e)
    | .ok result => checked := checked.push result
  match checked.back? with
  | some result => return result
  | none => throw .emptyProof

structure ClosedChecked (relation : ExprRel) (target : Statement) : Type where
  certificate : Nonempty (ProofTree relation target.sequent.1 target.sequent.2 ∅)

/-- Require the requested conclusion and no remaining assumed sequents. -/
def checkClosed (proof : LinearProof) (target : Statement) (external : Array Statement := #[]) :
    Except CheckError (ClosedChecked leq target) := do
  let result ← check proof external
  if htarget : result.statement.sequent = target.sequent then
    if hempty : result.assumptions = ∅ then
      return ⟨by
        have certificate := result.certificate
        rw [hempty, Finset.image_empty] at certificate
        have hpre := congrArg Prod.fst htarget
        have hpost := congrArg Prod.snd htarget
        rw [← hpre, ← hpost]
        exact certificate⟩
    else throw .unresolvedAssumptions
  else throw .wrongConclusion

end Checking

section Resolution

variable {leq : ExprRel}


/-- Resolve checked assumptions in a target calculus using positive order simulation. -/
theorem Checked.resolveWith {target : ExprRel}
    (result : Checked leq) (sim : Subrelation leq target)
    (imports : ∀ s ∈ result.assumptions,
      Nonempty (Weakened.ProofTree target s.sequent.1 s.sequent.2)) :
    Nonempty (Weakened.ProofTree target result.statement.sequent.1 result.statement.sequent.2) := by
  classical
  obtain ⟨tree⟩ := result.certificate
  have resolved : ∀ s ∈ result.assumptions.image Statement.sequent,
      Nonempty (Weakened.ProofTree target s.1 s.2) := by
    intro s hs
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp hs
    exact imports source hsource
  exact ⟨Imported.resolveWith sim tree (fun s hs => Classical.choice (resolved s hs))⟩

/-- Resolve the remaining imports of a checked result with supplied derivations. -/
theorem Checked.resolve (result : Checked leq)
    (imports : ∀ s ∈ result.assumptions,
      Nonempty (Weakened.ProofTree leq s.sequent.1 s.sequent.2)) :
    Nonempty (Weakened.ProofTree leq result.statement.sequent.1 result.statement.sequent.2) :=
  result.resolveWith ((fun h => h)) imports

/-- Transfer a closed certificate without transferring any negative order decisions. -/
theorem ClosedChecked.resolveWith {targetOrder : ExprRel}
    {statement : Statement} (result : ClosedChecked leq statement)
    (sim : Subrelation leq targetOrder) :
    Nonempty (Weakened.ProofTree targetOrder statement.sequent.1 statement.sequent.2) := by
  obtain ⟨tree⟩ := result.certificate
  exact ⟨Imported.resolveWith sim tree
    (fun s hs => False.elim (Finset.notMem_empty s hs))⟩

end Resolution

end Imported.Checker
