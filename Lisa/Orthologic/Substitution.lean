import Lisa.Orthologic.Calculus
import Lisa.Orthologic.Normalize

namespace Lisa.Orthologic

/-- Replace signed atoms by formulas, preserving their polarity. -/
def Nnf.bind {α β : Type} (f : α → Nnf β) : Nnf α → Nnf β
  | .lit a false => f a
  | .lit a true => (f a).compl
  | .bot => .bot
  | .top => .top
  | .meet p q => .meet (p.bind f) (q.bind f)
  | .join p q => .join (p.bind f) (q.bind f)

@[simp] theorem Nnf.eval_bind {α β L : Type} [Ortholattice L]
    (f : α → Nnf β) (v : β → L) (p : Nnf α) :
    (p.bind f).eval v = p.eval (fun a => (f a).eval v) := by
  induction p with
  | lit a s => cases s <;> simp [Nnf.bind, Nnf.eval]
  | _ => simp_all [Nnf.bind, Nnf.eval]

namespace Calculus

theorem Derives.bind {α β : Type} {p q : Nnf α}
    (h : Derives p q) (f : α → Nnf β) : Derives (p.bind f) (q.bind f) :=
  complete _ _ (fun _ _ v => by simpa using h.sound (fun a => (f a).eval v))

namespace Free

/-- Extend an atom valuation to the free ortholattice. -/
def lift {α L : Type} [Ortholattice L] (v : α → L) : Free α → L :=
  Quotient.lift (Nnf.eval v) (fun _ _ h => le_antisymm (h.1.sound v) (h.2.sound v))

@[simp] theorem lift_value {α L : Type} [Ortholattice L]
    (v : α → L) (p : Nnf α) : lift v (value p) = p.eval v := rfl

@[simp] theorem lift_inf {α L : Type} [Ortholattice L]
    (v : α → L) (p q : Free α) : lift v (p ⊓ q) = lift v p ⊓ lift v q :=
  Quotient.inductionOn₂ p q (fun _ _ => rfl)

@[simp] theorem lift_sup {α L : Type} [Ortholattice L]
    (v : α → L) (p q : Free α) : lift v (p ⊔ q) = lift v p ⊔ lift v q :=
  Quotient.inductionOn₂ p q (fun _ _ => rfl)

@[simp] theorem lift_compl {α L : Type} [Ortholattice L]
    (v : α → L) (p : Free α) : lift v pᶜ = (lift v p)ᶜ :=
  Quotient.inductionOn p (fun _ => Nnf.eval_compl v _)

@[simp] theorem lift_bot {α L : Type} [Ortholattice L]
    (v : α → L) : lift v ⊥ = ⊥ := rfl

@[simp] theorem lift_top {α L : Type} [Ortholattice L]
    (v : α → L) : lift v ⊤ = ⊤ := rfl

/-- Substitute quotient-valued formulas without choosing representatives. -/
def substitute {α β : Type} (f : α → Free β) : Free α → Free β := lift f

theorem substitute_id {α : Type} (p : Free α) :
    substitute (fun a => value (.lit a false)) p = p :=
  Quotient.inductionOn p eval_free

private theorem lift_eval {α β L : Type} [Ortholattice L]
    (f : α → Free β) (g : β → L) (p : Nnf α) :
    lift g (p.eval f) = p.eval (fun a => lift g (f a)) := by
  induction p with
  | lit a s => cases s <;> simp [Nnf.eval]
  | _ => simp_all [Nnf.eval]

theorem substitute_comp {α β γ : Type}
    (f : α → Free β) (g : β → Free γ) (p : Free α) :
    substitute g (substitute f p) = substitute (fun a => substitute g (f a)) p :=
  Quotient.inductionOn p (lift_eval f g)

end Free

/-- Preserve derivability in both directions when normalizing the operands. -/
theorem derives_normalize_iff {α : Type} [DecidableEq α] (p q : Nnf α) :
    Derives p.normalize q.normalize ↔ Derives p q := by
  constructor <;> intro h
  · exact complete _ _ (fun _ _ v => by simpa using h.sound v)
  · exact complete _ _ (fun _ _ v => by simpa using h.sound v)

end Calculus

end Lisa.Orthologic
