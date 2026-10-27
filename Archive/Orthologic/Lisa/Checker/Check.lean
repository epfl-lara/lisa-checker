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

variable {leq : ExprRel}

section Conditions

variable [SequentEncoding leq] [OrderReduction leq] [DecidableRel leq]

instance (p q : Expr) : Decidable (isSame leq p q) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (p : Expr) (Γ : Finset Expr) : Decidable (ordContains leq p Γ) :=
  inferInstanceAs (Decidable (∃ q ∈ Γ, isSame leq p q))
instance (p : Expr) : Decidable p.wellSorted :=
  inferInstanceAs (Decidable p.sort.isSome)
instance (p : Expr) : Decidable (isFormula p) :=
  inferInstanceAs (Decidable (p.sort = some prop))
instance (p : Expr) : Decidable (isTerm p) :=
  inferInstanceAs (Decidable (p.sort = some ind))
instance (Γ : Finset Expr) : Decidable (isFSet Γ) :=
  inferInstanceAs (Decidable (∀ p ∈ Γ, isFormula p))
private def decideSubst : (σ : Subst) → Decidable σ.wellSorted
  | .nil => isTrue trivial
  | .cons _ _ rest => @instDecidableAnd _ _ (inferInstanceAs (Decidable (_ = _))) (decideSubst rest)
instance (σ : Subst) : Decidable σ.wellSorted := decideSubst σ
instance (p q : Expr) : Decidable (reducedSame leq p q) :=
  if h : p = q then isTrue (h ▸ rfl)
  else inferInstanceAs (Decidable (_ = _))

omit [SequentEncoding leq] [DecidableRel leq] in
private theorem reducedSubset_image (Γ Δ : Finset Expr) :
    reducedSubset leq Γ Δ ↔
      Γ.image (OrderReduction.reduce (leq := leq)) ⊆
        Δ.image (OrderReduction.reduce (leq := leq)) := by
  constructor
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨r, hr, he⟩ := h q hq
    exact Finset.mem_image.mpr ⟨r, hr, he.symm⟩
  · intro h p hp
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    exact ⟨q, hq, he.symm⟩

/-- Normalize each context once after literal inclusion fails. -/
instance (Γ Δ : Finset Expr) : Decidable (reducedSubset leq Γ Δ) :=
  if h : Γ ⊆ Δ then isTrue (fun p hp => ⟨p, h hp, rfl⟩)
  else decidable_of_iff
    (Γ.image (OrderReduction.reduce (leq := leq)) ⊆
      Δ.image (OrderReduction.reduce (leq := leq)))
    (reducedSubset_image Γ Δ).symm

/-- Try equality of reduced contexts, then decide equivalence in the selected relation. -/
instance (Γ Δ : Finset Expr) : Decidable (setLeq leq Γ Δ) :=
  if h : reducedSubset leq Γ Δ then isTrue (setLeq_of_reducedSubset h)
  else inferInstanceAs (Decidable (∀ p ∈ Γ, ∃ q ∈ Δ, isSame leq p q))

instance (Γ Δ : Finset Expr) (p : Expr) : Decidable (containedExcept leq Γ Δ p) :=
  inferInstanceAs (Decidable (∀ q ∈ Γ, (∃ r ∈ Δ, isSame leq q r) ∨ isSame leq q p))

instance (Γ Δ : Finset Expr) (p q : Expr) : Decidable (containedExceptEither leq Γ Δ p q) :=
  inferInstanceAs (Decidable (∀ r ∈ Γ, (∃ s ∈ Δ, isSame leq r s) ∨ isSame leq r p ∨ isSame leq r q))

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

omit [SequentEncoding leq] [OrderReduction leq] [DecidableRel leq] in
private theorem image_dependencies (ps : List (Checked leq × Expr)) :
    (dependencies ps).image Statement.sequent =
      premiseAssumptions (ps.map annotated) := by
  induction ps with
  | nil => simp [dependencies, premiseAssumptions]
  | cons p ps ih =>
    simpa only [dependencies, List.foldr_cons, Finset.image_union,
      List.map_cons, premiseAssumptions, annotated] using congrArg
      (fun ss => p.1.assumptions.image Statement.sequent ∪ ss) ih

/-- Select a cheaper matching relation with certified transfer to the result relation. -/
structure Matching (target : ExprRel) where
  source : ExprRel
  reduction : OrderReduction source
  decision : DecidableRel source
  simulation : Subrelation source target

/-- Use the result relation itself for every match. -/
def Matching.exact (order : ExprRel) [OrderReduction order] [DecidableRel order] : Matching order :=
  ⟨order, inferInstance, inferInstance, (fun h => h)⟩

end Conditions

section Checking

variable [CheckerOrder leq]

/-- Check rule matches in a certified source relation; keep whole-sequent checks in the result relation. -/
def checkStepMatching (matching : Matching leq) (imports checked : Array (Checked leq)) (step : Step) :
    Except CheckError (Checked leq) := do
  letI := matching.reduction
  letI := matching.decision
  let source := matching.source
  let sim : Subrelation matching.source leq := matching.simulation
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
      letI := Statement.decideSame (leq := leq) p0.statement output
      if heq : sameSequent leq p0.statement.sequent output.sequent then
        letI : DecidablePred (fun s : Statement =>
            ¬ sameSequent leq s.sequent p1.statement.sequent) :=
          fun s => @instDecidableNot _ (Statement.decideSame s p1.statement)
        let remaining := p0.assumptions.filter fun s =>
          ¬ sameSequent leq s.sequent p1.statement.sequent
        return ⟨p0.statement, remaining ∪ p1.assumptions, by
          classical
          have himage : remaining.image Statement.sequent =
              discharged leq (p0.assumptions.image Statement.sequent) p1.statement.sequent := by
            ext s
            simp only [remaining, discharged, Finset.mem_image, Finset.mem_filter]
            aesop
          rw [Finset.image_union, himage]
          exact ⟨.discharge (Classical.choice p0.certificate) (Classical.choice p1.certificate)⟩⟩
      else throw .invalidConditions
    | .restate premise0 => do
      let p0 ← lookup imports checked premise0
      letI := Statement.decideLeq (leq := leq) p0.statement output
      letI := Statement.decideLeq (leq := leq) output p0.statement
      if h : (sequentLeq leq p0.statement.sequent.1 p0.statement.sequent.2 Ω₁ Ω₂) ∧
          (sequentLeq leq Ω₁ Ω₂ p0.statement.sequent.1 p0.statement.sequent.2) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, _⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.weakening hsort.1 hsort.2 tree0 h5⟩⟩
      else throw .invalidConditions
    | .weakening premise0 => do
      let p0 ← lookup imports checked premise0
      letI := Statement.decideLeq (leq := leq) p0.statement output
      if h : (sequentLeq leq p0.statement.sequent.1 p0.statement.sequent.2 Ω₁ Ω₂) then
        return ⟨output, p0.assumptions, by
          classical
          let tree0 := Classical.choice p0.certificate
          exact ⟨.weakening hsort.1 hsort.2 tree0 h⟩⟩
      else throw .invalidConditions
    | .restateTrue => do
      letI := Statement.decideTrue (leq := leq) output
      if h : (isSame leq (sequentToFormula Ω₁ Ω₂) top) then
        return ⟨output, ∅, by
          classical
          exact ⟨.restateTrue hsort.1 hsort.2 h⟩⟩
      else throw .invalidConditions
    | .hypothesis α => do
      if h : (isFormula α) ∧
          (ordContains source α Ω₁) ∧
          (ordContains source α Ω₂) then
        return ⟨output, ∅, by
          classical
          rcases h with ⟨h2, h3, h4⟩
          exact ⟨.hypothesis α
            hsort.1 hsort.2 h2
            (sim.member h3) (sim.member h4)⟩⟩
      else throw .invalidConditions
    | .cut premise0 premise1 α => do
      let p0 ← lookup imports checked premise0
      let p1 ← lookup imports checked premise1
      if h : (isFormula α) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (setLeq leq p1.statement.sequent.2 Ω₂) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ (α)) ∧
          (containedExcept source p1.statement.sequent.1 Ω₁ (α)) then
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨h8, h9, h10, h11, h12⟩
          let tree0 := Classical.choice p0.certificate
          let tree1 := Classical.choice p1.certificate
          rw [Finset.image_union]
          exact ⟨.cut α tree0 tree1
            hsort.1 hsort.2 h8 h9 h10
            (sim.except h11) (sim.except h12)⟩⟩
      else throw .invalidConditions
    | .leftAnd premise0 α β => do
      let p0 ← lookup imports checked premise0
      if h : (isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExceptEither source p0.statement.sequent.1 Ω₁ (α) (β)) ∧
          (ordContains source (and α β) Ω₁) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftAnd α β tree0
            hsort.1 hsort.2 h5 h6 h7
            (sim.exceptEither h8) (sim.member h9)⟩⟩
      else throw .invalidConditions
    | .leftOr references => do
      let ps ← references.mapM fun (ref, φ) => do
        let p ← lookup imports checked ref
        pure (p, φ)
      let prems := ps.map annotated
      if h : prems ≠ [] ∧
          (∀ prem ∈ prems, isFormula prem.val.1) ∧
          (∀ prem ∈ prems, setLeq leq prem.post Ω₂ ∧
            containedExcept source prem.pre Ω₁ prem.val.1) ∧
          ordContains source (foldFormulas or bot (prems.map (·.val.1))) Ω₁ then
        return ⟨output, dependencies ps, by
          classical
          rw [image_dependencies]
          refine ⟨.leftOr h.1 hsort.1 hsort.2 h.2.1 ?_
            (fun prem hp => ⟨(h.2.2.1 prem hp).1, sim.except (h.2.2.1 prem hp).2⟩)
            (sim.member h.2.2.2)⟩
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
      if h : (isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (setLeq leq p1.statement.sequent.2 Ω₂) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ (α)) ∧
          (containedExcept source p1.statement.sequent.1 Ω₁ (β)) ∧
          (ordContains source (imp α β) Ω₁) then
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨h8, h9, h10, h11, h12, h13, h14⟩
          let tree0 := Classical.choice p0.certificate
          let tree1 := Classical.choice p1.certificate
          rw [Finset.image_union]
          exact ⟨.leftImp α β tree0 tree1
            hsort.1 hsort.2 h8 h9 h10 h11
            (sim.except h12) (sim.except h13) (sim.member h14)⟩⟩
      else throw .invalidConditions
    | .leftIff premise0 α β => do
      let p0 ← lookup imports checked premise0
      if h : (isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExceptEither source p0.statement.sequent.1 Ω₁ ((imp α β)) ((imp β α))) ∧
          (ordContains source (iff α β) Ω₁) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftIff α β tree0
            hsort.1 hsort.2 h5 h6 h7
            (sim.exceptEither h8) (sim.member h9)⟩⟩
      else throw .invalidConditions
    | .leftNot premise0 α => do
      let p0 ← lookup imports checked premise0
      if h : (isFormula α) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ (α)) ∧
          (ordContains source (neg α) Ω₁) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftNot α tree0
            hsort.1 hsort.2 h5 h6
            (sim.except h7) (sim.member h8)⟩⟩
      else throw .invalidConditions
    | .leftForall premise0 x α t => do
      let p0 ← lookup imports checked premise0
      if h : (x.sort = ind) ∧
          (isFormula α) ∧
          (isTerm t) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept source p0.statement.sequent.1 Ω₁ ((substOne x t α))) ∧
          (ordContains source (forall_ x α) Ω₁) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftForall x α t tree0
            hsort.1 hsort.2 h5 h6 h7 h8
            (sim.except h9) (sim.member h10)⟩⟩
      else throw .invalidConditions
    | .leftExists premise0 x α => do
      let p0 ← lookup imports checked premise0
      if h : (x.sort = ind) ∧
          (isFormula α) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept source p0.statement.sequent.1 Ω₁ (α)) ∧
          (ordContains source (exists_ x α) Ω₁) ∧
          (x ∉ freeVars (Ω₁ ∪ Ω₂)) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftExists x α tree0
            hsort.1 hsort.2 h5 h6 h7
            (sim.except h8) (sim.member h9) h10⟩⟩
      else throw .invalidConditions
    | .rightAnd references => do
      let ps ← references.mapM fun (ref, φ) => do
        let p ← lookup imports checked ref
        pure (p, φ)
      let prems := ps.map annotated
      if h : prems ≠ [] ∧
          (∀ prem ∈ prems, isFormula prem.val.1) ∧
          (∀ prem ∈ prems, setLeq leq prem.pre Ω₁ ∧
            containedExcept source prem.post Ω₂ prem.val.1) ∧
          ordContains source (foldFormulas and top (prems.map (·.val.1))) Ω₂ then
        return ⟨output, dependencies ps, by
          classical
          rw [image_dependencies]
          refine ⟨.rightAnd h.1 hsort.1 hsort.2 h.2.1 ?_
            (fun prem hp => ⟨(h.2.2.1 prem hp).1, sim.except (h.2.2.1 prem hp).2⟩)
            (sim.member h.2.2.2)⟩
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
      if h : (isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExceptEither source p0.statement.sequent.2 Ω₂ (α) (β)) ∧
          (ordContains source (or α β) Ω₂) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightOr α β tree0
            hsort.1 hsort.2 h5 h6 h7
            (sim.exceptEither h8) (sim.member h9)⟩⟩
      else throw .invalidConditions
    | .rightImp premise0 α β => do
      let p0 ← lookup imports checked premise0
      if h : (isFormula α) ∧
          (isFormula β) ∧
          (containedExcept source p0.statement.sequent.1 Ω₁ (α)) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ (β)) ∧
          (ordContains source (imp α β) Ω₂) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightImp α β tree0
            hsort.1 hsort.2 h5 h6
            (sim.except h7) (sim.except h8) (sim.member h9)⟩⟩
      else throw .invalidConditions
    | .rightIff premise0 premise1 α β => do
      let p0 ← lookup imports checked premise0
      let p1 ← lookup imports checked premise1
      if h : (isFormula α) ∧
          (isFormula β) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (setLeq leq p1.statement.sequent.1 Ω₁) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ ((imp α β))) ∧
          (containedExcept source p1.statement.sequent.2 Ω₂ ((imp β α))) ∧
          (ordContains source (iff α β) Ω₂) then
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨h8, h9, h10, h11, h12, h13, h14⟩
          let tree0 := Classical.choice p0.certificate
          let tree1 := Classical.choice p1.certificate
          rw [Finset.image_union]
          exact ⟨.rightIff α β tree0 tree1
            hsort.1 hsort.2 h8 h9 h10 h11
            (sim.except h12) (sim.except h13) (sim.member h14)⟩⟩
      else throw .invalidConditions
    | .rightNot premise0 α => do
      let p0 ← lookup imports checked premise0
      if h : (isFormula α) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept source p0.statement.sequent.1 Ω₁ (α)) ∧
          (ordContains source (neg α) Ω₂) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightNot α tree0
            hsort.1 hsort.2 h5 h6
            (sim.except h7) (sim.member h8)⟩⟩
      else throw .invalidConditions
    | .rightForall premise0 x α => do
      let p0 ← lookup imports checked premise0
      if h : (x.sort = ind) ∧
          (isFormula α) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ (α)) ∧
          (ordContains source (forall_ x α) Ω₂) ∧
          (x ∉ freeVars (Ω₁ ∪ Ω₂)) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightForall x α tree0
            hsort.1 hsort.2 h5 h6 h7
            (sim.except h8) (sim.member h9) h10⟩⟩
      else throw .invalidConditions
    | .rightExists premise0 x α t => do
      let p0 ← lookup imports checked premise0
      if h : (x.sort = ind) ∧
          (isFormula α) ∧
          (isTerm t) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ ((substOne x t α))) ∧
          (ordContains source (exists_ x α) Ω₂) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightExists x α t tree0
            hsort.1 hsort.2 h5 h6 h7 h8
            (sim.except h9) (sim.member h10)⟩⟩
      else throw .invalidConditions
    | .rightEpsilon premise0 x α t => do
      let p0 ← lookup imports checked premise0
      if h : (x.sort = ind) ∧
          (isFormula α) ∧
          (isTerm t) ∧
          (setLeq leq p0.statement.sequent.1 Ω₁) ∧
          (containedExcept source p0.statement.sequent.2 Ω₂ ((substOne x t α))) ∧
          (ordContains source (substOne x (epsilon_ (.lam x α)) α) Ω₂) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9, h10⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.rightEpsilon x α t tree0
            hsort.1 hsort.2 h5 h6 h7 h8
            (sim.except h9) (sim.member h10)⟩⟩
      else throw .invalidConditions
    | .leftRefl premise0 s t => do
      let p0 ← lookup imports checked premise0
      if h : (isTerm s) ∧
          (isTerm t) ∧
          (isSame source s t) ∧
          (setLeq leq p0.statement.sequent.2 Ω₂) ∧
          (containedExcept source p0.statement.sequent.1 Ω₁ ((eq s t))) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6, h7, h8, h9⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.leftRefl s t tree0
            hsort.1 hsort.2 h5 h6
            (sim.same h7) h8 (sim.except h9)⟩⟩
      else throw .invalidConditions
    | .rightRefl s t => do
      if h : (isTerm s) ∧
          (isTerm t) ∧
          (isSame source s t) ∧
          (ordContains source (eq s t) Ω₂) then
        return ⟨output, ∅, by
          classical
          rcases h with ⟨h2, h3, h4, h5⟩
          exact ⟨.rightRefl s t
            hsort.1 hsort.2 h2 h3
            (sim.same h4) (sim.member h5)⟩⟩
      else throw .invalidConditions
    | .leftSubst premise comparison r => do
      let p0 ← lookup imports checked premise
      let p1 ← lookup imports checked comparison
      let Θ := p1.statement.sequent.1
      let Ξ := p1.statement.sequent.2.erase r.equation
      if h : r.valid ∧ r.equation ∈ p1.statement.sequent.2 ∧ r.fresh Θ Ξ ∧
          containedExcept source p0.statement.sequent.1 Ω₁ r.source ∧
          setLeq leq p0.statement.sequent.2 Ω₂ ∧ ordContains source r.target Ω₁ ∧
          setLeq leq Θ Ω₁ ∧ setLeq leq Ξ Ω₂ then
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨hv, he, hf, hl, hr, ha, hΘ, hΞ⟩
          rw [Finset.image_union]
          have comparisonTree : ProofTree leq Θ (insert r.equation Ξ)
              (p1.assumptions.image Statement.sequent) := by
            simpa only [Ξ, Finset.insert_erase he] using Classical.choice p1.certificate
          exact ⟨.leftSubst r (Classical.choice p0.certificate) comparisonTree
            hsort.1 hsort.2 hv hf (sim.except hl) hr (sim.member ha) hΘ hΞ⟩⟩
      else throw .invalidConditions
    | .rightSubst premise comparison r => do
      let p0 ← lookup imports checked premise
      let p1 ← lookup imports checked comparison
      let Θ := p1.statement.sequent.1
      let Ξ := p1.statement.sequent.2.erase r.equation
      if h : r.valid ∧ r.equation ∈ p1.statement.sequent.2 ∧ r.fresh Θ Ξ ∧
          setLeq leq p0.statement.sequent.1 Ω₁ ∧
          containedExcept source p0.statement.sequent.2 Ω₂ r.source ∧
          ordContains source r.target Ω₂ ∧ setLeq leq Θ Ω₁ ∧ setLeq leq Ξ Ω₂ then
        return ⟨output, p0.assumptions ∪ p1.assumptions, by
          classical
          rcases h with ⟨hv, he, hf, hl, hr, ha, hΘ, hΞ⟩
          rw [Finset.image_union]
          have comparisonTree : ProofTree leq Θ (insert r.equation Ξ)
              (p1.assumptions.image Statement.sequent) := by
            simpa only [Ξ, Finset.insert_erase he] using Classical.choice p1.certificate
          exact ⟨.rightSubst r (Classical.choice p0.certificate) comparisonTree
            hsort.1 hsort.2 hv hf hl (sim.except hr) (sim.member ha) hΘ hΞ⟩⟩
      else throw .invalidConditions
    | .instSchema premise0 σ => do
      let p0 ← lookup imports checked premise0
      if h : (Subst.wellSorted σ) ∧
          ((
        let Γ₁' := p0.statement.sequent.1.image (Subst.subst σ)
        let Γ₂' := p0.statement.sequent.2.image (Subst.subst σ)

        setLeq source Γ₁' Ω₁ ∧ setLeq source Γ₂' Ω₂
      )) then
        return ⟨output, p0.assumptions, by
          classical
          rcases h with ⟨h5, h6⟩
          let tree0 := Classical.choice p0.certificate
          exact ⟨.instSchema σ tree0
            hsort.1 hsort.2 h5 ⟨sim.members h6.1, sim.members h6.2⟩⟩⟩
      else throw .invalidConditions
  else throw .illSortedConclusion

/-- Check every condition in the result relation. -/
def checkStep (imports checked : Array (Checked leq)) (step : Step) :
    Except CheckError (Checked leq) :=
  checkStepMatching (.exact leq) imports checked step

/-- Retry failed cheap matches with the complete supplied result comparison. -/
def checkStepFallback (matching : Matching leq) (imports checked : Array (Checked leq)) (step : Step) :
    Except CheckError (Checked leq) :=
  match checkStepMatching matching imports checked step with
  | .error .invalidConditions => checkStep imports checked step
  | result => result

/-- Preserve exact checking when no cheaper matching relation is supplied. -/
theorem checkStepFallback_exact (imports checked : Array (Checked leq)) (step : Step) :
    checkStepFallback (.exact leq) imports checked step = checkStep imports checked step := by
  cases h : checkStepMatching (.exact leq) imports checked step with
  | ok result => simp [checkStepFallback, checkStep, h]
  | error e => cases e <;> simp [checkStepFallback, checkStep, h]

/-- Check every record; return the actual conclusion of the final checked step. -/
def check (proof : LinearProof) (external : Array Statement := #[])
    (matching : Matching leq := .exact leq) :
    Except CheckError (Checked leq) := do
  let imports ← external.mapM fun statement => checkStepFallback matching #[] #[] ⟨statement, .assume⟩
  let mut checked := #[]
  for step in proof do
    match checkStepFallback matching imports checked step with
    | .error e => throw (.atStep checked.size e)
    | .ok result => checked := checked.push result
  match checked.back? with
  | some result => return result
  | none => throw .emptyProof

structure ClosedChecked (leq : ExprRel) (target : Statement) : Type where
  certificate : Nonempty (ProofTree leq target.sequent.1 target.sequent.2 ∅)

/-- Require the requested conclusion and no remaining assumed sequents. -/
def checkClosed (proof : LinearProof) (target : Statement) (external : Array Statement := #[])
    (matching : Matching leq := .exact leq) :
    Except CheckError (ClosedChecked leq target) := do
  let result ← check (leq := leq) proof external matching
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
