import Lisa.ImportedWeakened

open Lisa Expr Imported

namespace Lisa.Tests.OrderSimulation

/-- Use syntactic equality to expose a strict simulation without logical assumptions. -/
private def literal : ExprRel := Eq
private def coarse : ExprRel := fun _ _ => True

private def simulation : Subrelation literal coarse :=
  fun _ => trivial

private def a : Expr := .const (.named "A" prop)
private def hole : Sequent := (∅, {a})
private def truth : Sequent := (∅, {top})

-- A target comparison may succeed where the source comparison fails.
private theorem source_keeps : discharged literal {hole} truth = {hole} := by
  simp [discharged, sameSequent, sequentLeq, sequentToFormula, disjunction,
    foldFormulas, literal, hole, truth, a, Expr.top, SConst.named]

private theorem target_removes : discharged coarse {hole} truth = ∅ := by
  simp [discharged, sameSequent, sequentLeq, coarse]

private noncomputable def source : ProofTree literal ∅ {a} {hole} := by
  have p : ProofTree literal ∅ {a} {hole} := .assume (by simp) (by simp [a])
  have q : ProofTree literal ∅ {top} ∅ := .restateTrue (by simp) (by simp [Expr.top])
    (by simp [isSame, sequentToFormula, disjunction, foldFormulas, literal])
  have result : ProofTree literal ∅ {a} (discharged literal {hole} truth ∪ ∅) :=
    .discharge p q
  simpa only [source_keeps, Finset.union_empty] using result

/-- Resolve the source's retained assumption, rather than recomputing the target filter. -/
noncomputable example : Weakened.ProofTree coarse ∅ {a} := by
  apply Imported.resolveWith simulation source
  intro s hs
  obtain rfl := Finset.mem_singleton.mp hs
  exact .restateTrue (by simp [hole]) (by simp [hole, a]) ⟨trivial, trivial⟩

example : discharged literal {hole} truth ≠ discharged coarse {hole} truth := by
  rw [source_keeps, target_removes]
  simp

#print axioms Imported.resolveWith

end Lisa.Tests.OrderSimulation
