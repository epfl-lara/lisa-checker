import Lisa.Orthologic.Structural

/-!
Flatten meets, reduce operands in their enclosing context, remove redundant
factors, and contract contradictions. Use only structural containment checks.
The dual operation handles joins. Follow the phases of Guilloud's `simplify`
and `check_for_contradiction`; prove preservation independently of completeness.
-/

namespace Lisa.Orthologic.Nnf

variable {α : Type}

/-- Reconstruct a meet, omitting the neutral element for nonempty lists. -/
def meetAll : List (Nnf α) → Nnf α
  | [] => .top
  | p :: ps => if ps.isEmpty then p else .meet p (meetAll ps)

@[simp] theorem eval_meetAll_cons {L : Type} [Ortholattice L]
    (v : α → L) (p : Nnf α) (ps : List (Nnf α)) :
    (meetAll (p :: ps)).eval v = p.eval v ⊓ (meetAll ps).eval v := by
  cases ps <;> simp [meetAll, eval]

@[simp] theorem eval_meetAll_nil {L : Type} [Ortholattice L] (v : α → L) :
    (meetAll ([] : List (Nnf α))).eval v = ⊤ := rfl

@[simp] theorem eval_meetAll_append {L : Type} [Ortholattice L]
    (v : α → L) (ps qs : List (Nnf α)) :
    (meetAll (ps ++ qs)).eval v = (meetAll ps).eval v ⊓ (meetAll qs).eval v := by
  induction ps <;> simp_all [inf_assoc]

@[simp] theorem eval_meetAll_reverse {L : Type} [Ortholattice L]
    (v : α → L) (ps : List (Nnf α)) :
    (meetAll ps.reverse).eval v = (meetAll ps).eval v := by
  induction ps <;> simp_all [inf_comm]

/-- Flatten nested meets and omit top factors. -/
def meetFactors : Nnf α → List (Nnf α)
  | .meet p q => meetFactors p ++ meetFactors q
  | .top => []
  | p => [p]

@[simp] theorem eval_meetFactors {L : Type} [Ortholattice L]
    (v : α → L) (p : Nnf α) : (meetAll p.meetFactors).eval v = p.eval v := by
  induction p <;> simp_all [meetFactors, eval]

variable [DecidableEq α]

/-- Refine a factor only when its enclosing meet implies the replacement. -/
def refineFactor (context : Nnf α) : Nnf α → List (Nnf α)
  | .meet p q => refineFactor context p ++ refineFactor context q
  | .join p q =>
      if structuralLe context p then refineFactor context p
      else if structuralLe context q then refineFactor context q
      else [.join p q]
  | .top => []
  | p => [p]

theorem eval_refineFactor {L : Type} [Ortholattice L]
    (v : α → L) (context p : Nnf α) :
    (meetAll (refineFactor context p)).eval v ≤ p.eval v ∧
    (context.eval v ≤ p.eval v →
      context.eval v ≤ (meetAll (refineFactor context p)).eval v) := by
  induction p with
  | meet p q ihp ihq =>
      simp only [refineFactor, eval_meetAll_append, eval]
      exact ⟨inf_le_inf ihp.1 ihq.1,
        fun h => le_inf (ihp.2 (h.trans inf_le_left)) (ihq.2 (h.trans inf_le_right))⟩
  | join p q ihp ihq =>
      simp only [refineFactor]
      split
      · rename_i h
        exact ⟨ihp.1.trans le_sup_left, fun _ => ihp.2 (structuralLe_sound v h)⟩
      · split
        · rename_i h
          exact ⟨ihq.1.trans le_sup_right, fun _ => ihq.2 (structuralLe_sound v h)⟩
        · simp
  | _ => simp [refineFactor, eval]

/-- Refine each factor in the same enclosing meet. -/
def refineFactors (context : Nnf α) (ps : List (Nnf α)) : List (Nnf α) :=
  ps.flatMap (refineFactor context)

theorem eval_refineFactors {L : Type} [Ortholattice L]
    (v : α → L) (context : Nnf α) (ps : List (Nnf α)) :
    (meetAll (refineFactors context ps)).eval v ≤ (meetAll ps).eval v ∧
    (context.eval v ≤ (meetAll ps).eval v →
      context.eval v ≤ (meetAll (refineFactors context ps)).eval v) := by
  induction ps with
  | nil => simp [refineFactors]
  | cons p ps ih =>
      simp only [refineFactors, List.flatMap_cons, eval_meetAll_append, eval_meetAll_cons]
      have hp := eval_refineFactor v context p
      exact ⟨inf_le_inf hp.1 ih.1,
        fun h => le_inf (hp.2 (h.trans inf_le_left)) (ih.2 (h.trans inf_le_right))⟩

theorem eval_refineFactors_self {L : Type} [Ortholattice L]
    (v : α → L) (ps : List (Nnf α)) :
    (meetAll (refineFactors (meetAll ps) ps)).eval v = (meetAll ps).eval v := by
  have h := eval_refineFactors v (meetAll ps) ps
  exact le_antisymm h.1 (h.2 le_rfl)

/-- Remove a factor when the remaining factors already imply it. -/
def pruneFactors (accepted : List (Nnf α)) : List (Nnf α) → List (Nnf α)
  | [] => accepted
  | p :: ps =>
      if structuralLe (meetAll (ps ++ accepted)) p then pruneFactors accepted ps
      else pruneFactors (p :: accepted) ps

theorem eval_pruneFactors {L : Type} [Ortholattice L]
    (v : α → L) (accepted ps : List (Nnf α)) :
    (meetAll (pruneFactors accepted ps)).eval v = (meetAll (ps ++ accepted)).eval v := by
  induction ps generalizing accepted with
  | nil => simp [pruneFactors]
  | cons p ps ih =>
      simp only [pruneFactors]
      split
      · rename_i h
        rw [ih]
        simp only [List.cons_append, eval_meetAll_cons]
        exact (inf_eq_right.mpr (structuralLe_sound v h)).symm
      · rw [ih]
        simp [inf_left_comm]

/-- Remove structurally redundant factors, then contract self-orthogonality. -/
def normalMeet (ps : List (Nnf α)) : Nnf α :=
  let refined := refineFactors (meetAll ps) ps
  let result := meetAll (pruneFactors [] refined).reverse
  if structuralLe result result.compl then .bot else result

@[simp] theorem eval_normalMeet {L : Type} [Ortholattice L]
    (v : α → L) (ps : List (Nnf α)) :
    (normalMeet ps).eval v = (meetAll ps).eval v := by
  unfold normalMeet
  dsimp only
  split
  · rename_i h
    have hbot := (Ortholattice.self_orth_iff _).mp (by
      simpa using structuralLe_sound v h)
    simpa [eval_pruneFactors, eval_refineFactors_self, eval] using hbot.symm
  · simp [eval_pruneFactors, eval_refineFactors_self]

end Lisa.Orthologic.Nnf
