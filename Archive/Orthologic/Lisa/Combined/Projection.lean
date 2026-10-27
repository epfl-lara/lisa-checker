import Lisa.Orthologic.ExpressionModel
import Lisa.Combined.Propositional
import Lisa.Orthologic.Decision
import Lisa.Orthologic.Substitution

/-!
Lift an executable atom interpretation through the propositional shell.

The shell consumes no contextual reduction budget. Its order laws follow from
the verified pure-OL engine, independently of how atoms are processed. Soundness
of the atom interpretation is a separate, one-way obligation.
-/

namespace Lisa.Orthologic.Projection

open Expr

/-- Interpret opaque expressions, possibly exposing further propositional structure. -/
abbrev Atoms (α : Type) := Expr → Nnf α

/-- Preserve the outer logical constructors while interpreting their opaque leaves. -/
def project (atoms : Atoms α) (p : Expr) : Nnf α :=
  (reify p).toNnf.bind atoms

/-- Evaluate the propositional shell under a supplied atom interpretation. -/
def eval {L : Type} [Ortholattice L] (atoms : Atoms α) (v : α → L) (p : Expr) : L :=
  (reify p).eval (fun a => (atoms a).eval v)

@[simp] theorem eval_project {L : Type} [Ortholattice L]
    (atoms : Atoms α) (v : α → L) (p : Expr) :
    (project atoms p).eval v = eval atoms v p := by
  simp [project, eval]

/-- Interpret expression order in one chosen model of the projected atoms. -/
@[reducible] def model {L : Type} [Ortholattice L] (atoms : Atoms α) (v : α → L) : Interpretation (fun p q => eval atoms v p ≤ eval atoms v q) where
  Carrier := L
  algebra := inferInstance
  eval := eval atoms v
  compare := fun _ _ => Iff.rfl
  top_eq := rfl
  bot_eq := rfl
  and_eq := fun _ _ => rfl
  or_eq := fun _ _ => rfl
  neg_eq := fun _ => rfl
  imp_eq := fun _ _ => rfl
  iff_eq := fun _ _ => rfl

/-- Compare projected formulas with the verified total pure-OL procedure. -/
def check [DecidableEq α] (atoms : Atoms α) (p q : Expr) : Bool :=
  Calculus.decideLe (project atoms p) (project atoms q)

/-- Specify the executable relation without assuming semantic completeness. -/
def leq [DecidableEq α] [Hashable α] (atoms : Atoms α) : ExprRel :=
  fun p q => check atoms p q = true

instance [DecidableEq α] [Hashable α] (atoms : Atoms α) : DecidableRel (leq atoms) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- Interpret projected expressions in the already verified free ortholattice. -/
def value (atoms : Atoms α) (p : Expr) : Calculus.Free α :=
  eval atoms (fun a => Calculus.value (.lit a false)) p

theorem check_iff_value_le [DecidableEq α] [Hashable α]
    (atoms : Atoms α) (p q : Expr) :
    check atoms p q = true ↔ value atoms p ≤ value atoms q := by
  rw [check, Calculus.decideLe_iff]
  change _ ↔ eval atoms _ p ≤ eval atoms _ q
  rw [← eval_project, ← eval_project, Calculus.eval_free, Calculus.eval_free]
  rfl

/-- Derive structural interfaces from the free-OL interpretation of projected syntax. -/
def interpretation [DecidableEq α] [Hashable α] (atoms : Atoms α) : Lisa.Orthologic.Interpretation (leq atoms) where
  Carrier := Calculus.Free α
  algebra := inferInstance
  eval := value atoms
  compare := check_iff_value_le atoms
  top_eq := rfl
  bot_eq := rfl
  and_eq := fun _ _ => rfl
  or_eq := fun _ _ => rfl
  neg_eq := fun _ => rfl
  imp_eq := fun _ _ => rfl
  iff_eq := fun _ _ => rfl

instance [DecidableEq α] [Hashable α] (atoms : Atoms α) : IsPreorder Expr (leq atoms) := (interpretation atoms).preorder
instance [DecidableEq α] [Hashable α] (atoms : Atoms α) : SequentEncoding (leq atoms) := (interpretation atoms).sequentEncoding

/-- Retain the independently certified propositional reducer. -/
instance [DecidableEq α] [Hashable α] (atoms : Atoms α) : OrderReduction (leq atoms) :=
  Orthologic.reduction (leq atoms) (interpretation atoms)

/-- Preserve the target interpretation when every atom interpretation does. -/
theorem eval_eq {order : ExprRel} (m : Interpretation order)
    (atoms : Atoms α) (v : α → m.Carrier)
    (sound : ∀ a, (atoms a).eval v = m.eval a) (p : Expr) :
    eval atoms v p = m.eval p := by
  unfold eval
  simpa only [sound] using eval_reify m p

/-- Certify positive answers in another expression order, without reflecting failures. -/
theorem sound [DecidableEq α] [Hashable α] {order : ExprRel} (m : Interpretation order)
    (atoms : Atoms α) (v : α → m.Carrier)
    (hsound : ∀ a, (atoms a).eval v = m.eval a)
    {p q : Expr} (h : leq atoms p q) : order p q := by
  have hv := (Calculus.decideLe_valid _ _).mp h
    (m.Carrier) v
  rw [eval_project, eval_project, eval_eq m atoms v hsound, eval_eq m atoms v hsound] at hv
  exact (m.compare p q).mpr hv

instance [DecidableEq α] [Hashable α] (atoms : Atoms α) : CheckerOrder (leq atoms) :=
  CheckerOrder.of _

end Lisa.Orthologic.Projection
