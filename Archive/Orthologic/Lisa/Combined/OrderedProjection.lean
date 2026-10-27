import Lisa.Combined.Projection
import Lisa.Orthologic.AtomicOrder

/-!
Lift an atomic preorder through the outer logical constructors.

Derive the three sequent interfaces from monotone interpretations, rather than
requiring an ortholattice structure on the combined expression relation.
Only the atomic comparison needs reflexivity, transitivity, and a decision
procedure. Its interpretation in the reference calculus is a separate obligation.
-/

namespace Lisa.Orthologic.OrderedProjection

open Projection

variable {α : Type} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] [IsPreorder α r] (atoms : Atoms α)

/-- Compare projected formulas using their finite atomic preorder constraints. -/
def check (p q : Expr) : Bool :=
  AtomicOrder.check r (project atoms p) (project atoms q)

/-- Specify the executable relation on expressions. -/
def leq : ExprRel := fun p q => check r atoms p q = true

instance : DecidableRel (leq r atoms) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- Interpret this order in every monotone valuation of its atoms. -/
theorem leq_iff (p q : Expr) :
    leq r atoms p q ↔ ∀ (L : Type) [Ortholattice L] (v : α → L),
      AtomicOrder.Valid r v → eval atoms v p ≤ eval atoms v q := by
  simp only [leq, check, AtomicOrder.check_valid, eval_project]

instance : IsPreorder Expr (leq r atoms) where
  refl p := (leq_iff r atoms p p).mpr (fun _ _ _ _ => le_rfl)
  trans p q s hp hq := (leq_iff r atoms p s).mpr (fun L _ v hv =>
    le_trans ((leq_iff r atoms p q).mp hp L v hv) ((leq_iff r atoms q s).mp hq L v hv))

omit [DecidableEq α] in
private theorem eval_listSequent {L : Type} [Ortholattice L] (v : α → L)
    (pre post : List Expr) :
    eval atoms v (listSequentToFormula pre post) =
      eval atoms v (sequentToFormula pre.toFinset post.toFinset) := by
  exact (model atoms v).listSequent pre post

instance : SequentEncoding (leq r atoms) where
  compare pre post p := by
    simp only [leq_iff, eval_listSequent, iff_self, and_self]

instance : OrderReduction (leq r atoms) :=
  OrderReduction.of
    reduceExpr
    (fun p => by
      constructor
      all_goals
        apply (leq_iff r atoms _ _).mpr
        intro L _ v _
        have h := same_reduceExpr (model atoms v) p
        first | exact h.1 | exact h.2)
    sort_reduceExpr

/-- Transfer positive comparisons through a sound monotone atomic interpretation. -/
theorem sound {order : ExprRel} (m : Interpretation order)
    (v : α → m.Carrier)
    (hv : AtomicOrder.Valid r v)
    (hsound : ∀ a, (atoms a).eval v = m.eval a)
    {p q : Expr} (h : leq r atoms p q) : order p q := by
  have h' := (leq_iff r atoms p q).mp h (m.Carrier) v hv
  rw [eval_eq m atoms v hsound, eval_eq m atoms v hsound] at h'
  exact (m.compare p q).mpr h'

instance  : CheckerOrder (leq r atoms) :=
  CheckerOrder.of _

end Lisa.Orthologic.OrderedProjection
