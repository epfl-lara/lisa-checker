import Lisa.Orthologic.Antichain

namespace Lisa.Orthologic

namespace Nnf

variable {α : Type} [DecidableEq α]

/-- Flatten and reduce a meet using structural normal-form comparisons. -/
def smartMeet (p q : Nnf α) : Nnf α :=
  normalMeet (p.meetFactors ++ q.meetFactors)

@[simp] theorem eval_smartMeet {L : Type} [Ortholattice L]
    (v : α → L) (p q : Nnf α) : (smartMeet p q).eval v = p.eval v ⊓ q.eval v := by
  simp [smartMeet]

/-- Simplify a join by dualizing the verified meet simplifier. -/
def smartJoin (p q : Nnf α) : Nnf α := (smartMeet p.compl q.compl).compl

@[simp] theorem eval_smartJoin {L : Type} [Ortholattice L]
    (v : α → L) (p q : Nnf α) : (smartJoin p q).eval v = p.eval v ⊔ q.eval v := by
  simp [smartJoin]

/-- Normalize bottom-up without distributing meets over joins. -/
def normalize : Nnf α → Nnf α
  | .lit a s => .lit a s
  | .bot => .bot
  | .top => .top
  | .meet p q => smartMeet p.normalize q.normalize
  | .join p q => smartJoin p.normalize q.normalize

@[simp] theorem eval_normalize {L : Type} [Ortholattice L]
    (v : α → L) (p : Nnf α) : p.normalize.eval v = p.eval v := by
  induction p <;> simp_all [normalize, eval]

/-- Preserve both directions of an inequality when normalizing its operands. -/
theorem normalize_le_iff {L : Type} [Ortholattice L]
    (v : α → L) (p q : Nnf α) :
    p.normalize.eval v ≤ q.normalize.eval v ↔ p.eval v ≤ q.eval v := by
  simp

/-- Discharge containment by structural comparison of reduced operands. -/
def checkNormalizedLe (p q : Nnf α) : Bool :=
  structuralLe p.normalize q.normalize

theorem checkNormalizedLe_sound {L : Type} [Ortholattice L]
    (v : α → L) {p q : Nnf α} (h : checkNormalizedLe p q = true) :
    p.eval v ≤ q.eval v := by
  simpa using structuralLe_sound v h

omit [DecidableEq α] in
/-- Reconstruct an expression with negation only on negative literals. -/
def toFormula : Nnf α → Formula α
  | .lit a false => .atom a
  | .lit a true => .neg (.atom a)
  | .bot => .bot
  | .top => .top
  | .meet p q => .meet p.toFormula q.toFormula
  | .join p q => .join p.toFormula q.toFormula

omit [DecidableEq α] in
@[simp] theorem toNnf_toFormula (p : Nnf α) : p.toFormula.toNnf = p := by
  induction p with
  | lit a s => cases s <;> rfl
  | _ => simp_all [toFormula, Formula.toNnf]

omit [DecidableEq α] in
@[simp] theorem eval_toFormula {L : Type} [Ortholattice L]
    (v : α → L) (p : Nnf α) : p.toFormula.eval v = p.eval v := by
  rw [← Formula.eval_toNnf, toNnf_toFormula]

end Nnf

/-- Eliminate nested negations and simplify using certified OL comparisons. -/
def Formula.normalize {α : Type} [DecidableEq α]
    (p : Formula α) : Nnf α := p.toNnf.normalize

@[simp] theorem Formula.eval_normalize {α L : Type} [DecidableEq α]
    [Ortholattice L] (v : α → L) (p : Formula α) : p.normalize.eval v = p.eval v := by
  simp [normalize]

end Lisa.Orthologic
