import Lisa.Orthologic.Algebra

namespace Lisa.Orthologic

/-- Represent ortholattice expressions independently of the atom language. -/
inductive Formula (α : Type) where
  | atom : α → Formula α
  | bot : Formula α
  | top : Formula α
  | meet : Formula α → Formula α → Formula α
  | join : Formula α → Formula α → Formula α
  | neg : Formula α → Formula α
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Keep negation only on atoms. Do not impose distributivity. -/
inductive Nnf (α : Type) where
  | lit : α → Bool → Nnf α
  | bot : Nnf α
  | top : Nnf α
  | meet : Nnf α → Nnf α → Nnf α
  | join : Nnf α → Nnf α → Nnf α
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Formula

def eval {α L : Type} [Ortholattice L] (v : α → L) : Formula α → L
  | .atom a => v a
  | .bot => ⊥
  | .top => ⊤
  | .meet p q => eval v p ⊓ eval v q
  | .join p q => eval v p ⊔ eval v q
  | .neg p => (eval v p)ᶜ

/-- Change an atom representation without changing propositional structure. -/
def map {α β : Type} (f : α → β) : Formula α → Formula β
  | .atom a => .atom (f a)
  | .bot => .bot
  | .top => .top
  | .meet p q => .meet (p.map f) (q.map f)
  | .join p q => .join (p.map f) (q.map f)
  | .neg p => .neg (p.map f)

@[simp] theorem eval_map {α β L : Type} [Ortholattice L]
    (f : α → β) (v : β → L) (p : Formula α) :
    (p.map f).eval v = p.eval (fun a => v (f a)) := by
  induction p <;> simp_all [Formula.map, Formula.eval]

end Formula

namespace Nnf

def eval {α L : Type} [Ortholattice L] (v : α → L) : Nnf α → L
  | .lit a false => v a
  | .lit a true => (v a)ᶜ
  | .bot => ⊥
  | .top => ⊤
  | .meet p q => eval v p ⊓ eval v q
  | .join p q => eval v p ⊔ eval v q

/-- Dualize connectives and flip literal polarity. -/
def compl {α : Type} : Nnf α → Nnf α
  | .lit a s => .lit a (!s)
  | .bot => .top
  | .top => .bot
  | .meet p q => .join (compl p) (compl q)
  | .join p q => .meet (compl p) (compl q)

@[simp] theorem compl_compl {α : Type} (p : Nnf α) : p.compl.compl = p := by
  induction p <;> simp_all [compl]

@[simp] theorem eval_compl {α L : Type} [Ortholattice L] (v : α → L) (p : Nnf α) :
    p.compl.eval v = (p.eval v)ᶜ := by
  induction p with
  | lit a s => cases s <;> simp [compl, eval]
  | _ => simp_all [compl, eval]

def size {α : Type} : Nnf α → Nat
  | .lit .. | .bot | .top => 1
  | .meet p q | .join p q => p.size + q.size + 1

@[simp] theorem size_compl {α : Type} (p : Nnf α) : p.compl.size = p.size := by
  induction p <;> simp_all [size, compl]

end Nnf

/-- Push negation through lattice operations using De Morgan's laws. -/
def Formula.toNnf {α : Type} : Formula α → Nnf α
  | .atom a => .lit a false
  | .bot => .bot
  | .top => .top
  | .meet p q => .meet p.toNnf q.toNnf
  | .join p q => .join p.toNnf q.toNnf
  | .neg p => p.toNnf.compl

@[simp] theorem Formula.eval_toNnf {α L : Type} [Ortholattice L]
    (v : α → L) (p : Formula α) : p.toNnf.eval v = p.eval v := by
  induction p <;> simp_all [Formula.toNnf, Nnf.eval, Formula.eval]

end Lisa.Orthologic
