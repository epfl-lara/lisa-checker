import Lisa.Combined
import Lisa.Orthologic.Memo

/-! Retain the combined checker's decisions while sharing scoped OL caches. -/

namespace Lisa.Combined.Cached

open Orthologic

private abbrev Answer (b : Bool) := {r : Bool // r = b}

private def contextual (budget : Nat) (p q : Expr) :
    StateM (Nnf.Memo Expr) (Answer (Combined.check budget p q)) := do
  if h : p = q then
    return ⟨true, by simp [Combined.check, h]⟩
  else
    let answer ← Nnf.checkMemo (Projection.project (atoms budget) p)
      (Projection.project (atoms budget) q)
    return ⟨if answer.val then true else ContextualProjection.check (contextualAtoms budget) p q,
      by simp [Combined.check, h, ← answer.property]⟩

private def constrained (r : Expr → Expr → Prop) [DecidableRel r]
    (p q : Nnf Expr) : StateM (Nnf.Memo Expr) (Answer (AtomicOrder.check r p q)) := do
  let first ← Nnf.checkMemo p q
  if h : first.val = true then
    return ⟨true, by simp [AtomicOrder.check, ← first.property, h]⟩
  else
    let support := (p.atoms ++ q.atoms).eraseDups
    let answer ← Nnf.checkMemo (p.bind (Constraints.encode support r))
      (q.bind (Constraints.encode support r))
    return ⟨answer.val, by
      simp only [AtomicOrder.check, ← first.property, if_neg h]
      rw [Constraints.check, answer.property]
      rfl⟩

private def quantified (budget depth : Nat) (p q : Expr) :
    StateM (Nnf.Memo Expr) (Answer (Quantified.check budget depth p q)) := do
  if h : p = q then
    return ⟨true, by simp [Quantified.check, h]⟩
  else
    let left := Projection.project (atoms budget) p
    let right := Projection.project (atoms budget) q
    let first ← Nnf.checkMemo left right
    if k : first.val = true then
      return ⟨true, by simp [Quantified.check, h, ← first.property, left, right, k]⟩
    else
      let answer ← constrained
        (QuantifiedProjection.atomicOrder (Combined.leq budget) (atoms budget) depth) left right
      return ⟨answer.val, by
        simp only [Quantified.check, if_neg h, OrderedProjection.check]
        change answer.val = if Nnf.checkNormalizedLe left right then true else _
        rw [← first.property, if_neg k]
        exact answer.property⟩

/-- Share normal forms and comparison pairs across replay's fallback backends. -/
def replay (budget : Nat) (p q : Expr) :
    StateM (Nnf.Memo Expr) (Answer (Replay.check budget p q)) := do
  let first ← contextual budget p q
  if h : first.val = true then
    return ⟨true, by simp [Replay.check, ← first.property, h]⟩
  else
    let second ← quantified budget (budget + 1) p q
    return ⟨second.val, by
      simp [Replay.check, ← first.property, Bool.eq_false_iff.mpr h, second.property]⟩

/-- Run replay with a fresh cache and the selected retention policy. -/
def check (config : Nnf.MemoConfig) (budget : Nat) (p q : Expr) : Bool :=
  ((replay budget p q).run' { config }).val

/-- Preserve every acceptance and rejection of the uncached replay checker. -/
theorem check_eq (config : Nnf.MemoConfig) (budget : Nat) (p q : Expr) :
    check config budget p q = Replay.check budget p q :=
  ((replay budget p q).run' { config }).property

@[reducible] private def decision (config : Nnf.MemoConfig) (budget : Nat) :
    DecidableRel (Replay.leq budget) := fun p q =>
  decidable_of_iff (check config budget p q = true)
    (by rw [check_eq]; exact Replay.check_iff budget p q)

private def matching (config : Nnf.MemoConfig) (budget : Nat) :
    Imported.Checker.Matching (Replay.leq budget) where
  source := Combined.leq budget
  reduction := inferInstance
  decision := fun p q =>
    let answer := ((contextual budget p q).run' { config }).val
    decidable_of_iff (answer = true)
      (by change (((contextual budget p q).run' { config }).val = true) ↔ _
          rw [((contextual budget p q).run' { config }).property]
          exact Combined.check_iff budget p q)
  simulation := Or.inl

/-- Read and check proofs using cached decisions for the unchanged replay relation. -/
def checkFiles (config : Nnf.MemoConfig) (budget : Nat)
    (treePath proofPath : System.FilePath) (diagnostics := false) :=
  letI := decision config budget
  letI : CheckerOrder (Replay.leq budget) := CheckerOrder.of _
  Imported.Binary.checkFiles (leq := Replay.leq budget)
    treePath proofPath diagnostics (matching config budget)

/-- Check a linear proof with cached decisions and the unchanged Imported certificate. -/
def checkProof (config : Nnf.MemoConfig) (budget : Nat)
    (proof : Imported.Checker.LinearProof) (imports : Array Imported.Checker.Statement := #[]) :=
  letI := decision config budget
  letI : CheckerOrder (Replay.leq budget) := CheckerOrder.of _
  Imported.Checker.check (leq := Replay.leq budget) proof imports (matching config budget)

end Lisa.Combined.Cached
