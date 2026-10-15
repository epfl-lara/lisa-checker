import Lisa.Combined.Propositional
import Lisa.Orthologic.ContextualCalculus

namespace Lisa.Orthologic.ContextualProjection

open Expr Contextual

/-- Replace formula leaves while retaining their propositional structure. -/
def embed (atoms : α → Term β κ) : Formula α → Term β κ
  | .atom a => atoms a
  | .bot => .bot
  | .top => .top
  | .meet p q => .meet (embed atoms p) (embed atoms q)
  | .join p q => .join (embed atoms p) (embed atoms q)
  | .neg p => .neg (embed atoms p)

@[simp] theorem eval_embed {L : Type} [Ortholattice L]
    (atoms : α → Term β κ) (v : β → L) (u : κ → L → L)
    (b : κ → L → L → L) (p : Formula α) :
    (embed atoms p).eval v u b = p.eval (fun a => (atoms a).eval v u b) := by
  induction p <;> simp_all [embed, Term.eval, Formula.eval]

/-- Expose the propositional shell without spending any contextual budget. -/
def project (atoms : Expr → Term α κ) (p : Expr) : Term α κ :=
  embed atoms (reify p)

/-- Evaluate the projected shell in the contextual quotient. -/
def eval (atoms : Expr → Term α κ) (p : Expr) : TheoryModel α κ :=
  (reify p).eval (fun a => Contextual.value (atoms a))

@[simp] theorem value_embed (atoms : α → Term β κ) (p : Formula α) :
    Contextual.value (embed atoms p) = p.eval (fun a => Contextual.value (atoms a)) := by
  induction p with
  | atom | bot | top => rfl
  | meet p q hp hq =>
      change Contextual.value (embed atoms p) ⊓ Contextual.value (embed atoms q) = _
      rw [hp, hq]
      rfl
  | join p q hp hq =>
      change Contextual.value (embed atoms p) ⊔ Contextual.value (embed atoms q) = _
      rw [hp, hq]
      rfl
  | neg p hp =>
      change (Contextual.value (embed atoms p))ᶜ = _
      rw [hp]
      rfl

/-- Decide contextual OL at the full constructor depth of the projected formulas. -/
def check [DecidableEq α] [DecidableEq κ]
    (atoms : Expr → Term α κ) (p q : Expr) : Bool :=
  if p = q then true else Contextual.check (project atoms p) (project atoms q)

/-- Specify exactly the answers of contextual comparison. -/
abbrev leq [DecidableEq α] [DecidableEq κ] (atoms : Expr → Term α κ) : Order :=
  fun p q => check atoms p q = true

instance [DecidableEq α] [DecidableEq κ] (atoms : Expr → Term α κ) :
    DecidableRel (leq atoms) := fun _ _ => inferInstanceAs (Decidable (_ = _))

theorem check_iff_eval_le [DecidableEq α] [DecidableEq κ]
    (atoms : Expr → Term α κ) (p q : Expr) :
    check atoms p q = true ↔ eval atoms p ≤ eval atoms q := by
  unfold check
  split
  · rename_i h
    subst q
    simp
  · rw [Contextual.check_iff, ← Contextual.value_le]
    simp only [project, value_embed, eval]

/-- Derive the checker interfaces from the contextual term model. -/
instance [DecidableEq α] [DecidableEq κ] (atoms : Expr → Term α κ) :
    OrderAlgebra (leq atoms) where
  Carrier := TheoryModel α κ
  algebra := inferInstance
  eval := eval atoms
  compare := check_iff_eval_le atoms
  top_eq := rfl
  bot_eq := rfl
  and_eq := fun _ _ => rfl
  or_eq := fun _ _ => rfl
  neg_eq := fun _ => rfl
  imp_eq := fun _ _ => rfl
  iff_eq := fun _ _ => rfl

instance [DecidableEq α] [DecidableEq κ] (atoms : Expr → Term α κ) :
    OrderReduction (leq atoms) := Orthologic.reduction (leq atoms)

/-- Transfer accepted comparisons when the contextual leaves preserve interpretation. -/
theorem sound [DecidableEq α] [DecidableEq κ] {order : Order} [OrderAlgebra order]
    (atoms : Expr → Term α κ)
    (v : α → OrderAlgebra.Carrier (leq := order))
    (u : κ → OrderAlgebra.Carrier (leq := order) → OrderAlgebra.Carrier (leq := order))
    (b : κ → OrderAlgebra.Carrier (leq := order) →
      OrderAlgebra.Carrier (leq := order) → OrderAlgebra.Carrier (leq := order))
    (hsound : ∀ a, (atoms a).eval v u b = OrderAlgebra.eval (leq := order) a)
    {p q : Expr} (h : leq atoms p q) : order p q := by
  have hc : Contextual.check (project atoms p) (project atoms q) = true := by
    rw [Contextual.check_iff, ← Contextual.value_le]
    simpa only [project, value_embed, eval] using (check_iff_eval_le atoms p q).mp h
  have hv := (Contextual.check_valid _ _).mp hc
    (OrderAlgebra.Carrier (leq := order)) v u b
  simp only [project, eval_embed, hsound, eval_reify] at hv
  exact (OrderAlgebra.compare p q).mpr hv

instance [DecidableEq α] [DecidableEq κ] (atoms : Expr → Term α κ) : CheckerOrder (leq atoms) :=
  CheckerOrder.of _

end Lisa.Orthologic.ContextualProjection
