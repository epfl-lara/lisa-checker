import Lisa.Orthologic.Substitution
import Lisa.Orthologic.Free

/-!
Decide OL with uninterpreted unary and binary constructors.
Use one free-OL layer per constructor depth; lattice connectives consume no layer.
This is not yet the lambda quotient: beta and eta impose additional equations.
-/

namespace Lisa.Orthologic.Contextual

inductive Term (α κ : Type) where
  | atom : α → Term α κ
  | bot | top : Term α κ
  | meet : Term α κ → Term α κ → Term α κ
  | join : Term α κ → Term α κ → Term α κ
  | neg : Term α κ → Term α κ
  | unary : κ → Term α κ → Term α κ
  | binary : κ → Term α κ → Term α κ → Term α κ
  deriving DecidableEq, Repr

/-- Count constructor nesting, not propositional formula size. -/
def Term.depth : Term α κ → Nat
  | .atom _ | .bot | .top => 0
  | .meet p q | .join p q => max p.depth q.depth
  | .neg p => p.depth
  | .unary _ p => p.depth + 1
  | .binary _ p q => max p.depth q.depth + 1

def Term.eval {L : Type} [Ortholattice L] (v : α → L)
    (u : κ → L → L) (b : κ → L → L → L) : Term α κ → L
  | .atom a => v a
  | .bot => ⊥
  | .top => ⊤
  | .meet p q => p.eval v u b ⊓ q.eval v u b
  | .join p q => p.eval v u b ⊔ q.eval v u b
  | .neg p => (p.eval v u b)ᶜ
  | .unary k p => u k (p.eval v u b)
  | .binary k p q => b k (p.eval v u b) (q.eval v u b)

inductive Label (α κ X : Type) where
  | atom : α → Label α κ X
  | unary : κ → X → Label α κ X
  | binary : κ → X → X → Label α κ X
  deriving DecidableEq

/-- Represent constructor arguments by values in the preceding free-OL layer. -/
def Labels (α κ : Type) : Nat → Type
  | 0 => α
  | n + 1 => Label α κ (Calculus.Free (Labels α κ n))

abbrev Carrier (α κ : Type) (n : Nat) := Calculus.Free (Labels α κ n)

open Calculus (Free)

private def literal {α : Type} (a : α) : Free α := Calculus.value (.lit a false)

/-- Extend a valuation monotonically to its free-OL carrier. -/
private theorem lift_mono {α L : Type} [Ortholattice L] (v : α → L) :
    Monotone (Free.lift v) := by
  intro p q h
  have he : p ⊓ q = p := inf_eq_left.mpr h
  have h' := congrArg (Free.lift v) he
  rw [Free.lift_inf] at h'
  exact inf_eq_left.mp h'

/-- Forget the deepest constructor arguments, preserving the OL structure. -/
def project (n : Nat) : Carrier α κ (n + 1) → Carrier α κ n :=
  match n with
  | 0 => Free.lift (fun
      | .atom a => literal a
      | .unary _ _ | .binary _ _ _ => ⊥)
  | n + 1 => Free.lift (fun
      | .atom a => literal (.atom a)
      | .unary k p => literal (.unary k (project n p))
      | .binary k p q => literal (.binary k (project n p) (project n q)))

@[simp] theorem project_inf (n : Nat) (p q : Carrier α κ (n + 1)) :
    project n (p ⊓ q) = project n p ⊓ project n q := by
  cases n <;> exact Free.lift_inf _ _ _

@[simp] theorem project_sup (n : Nat) (p q : Carrier α κ (n + 1)) :
    project n (p ⊔ q) = project n p ⊔ project n q := by
  cases n <;> exact Free.lift_sup _ _ _

@[simp] theorem project_compl (n : Nat) (p : Carrier α κ (n + 1)) :
    project n pᶜ = (project n p)ᶜ := by
  cases n <;> exact Free.lift_compl _ _

@[simp] theorem project_bot (n : Nat) : project (α := α) (κ := κ) n ⊥ = ⊥ := by
  cases n <;> rfl

@[simp] theorem project_top (n : Nat) : project (α := α) (κ := κ) n ⊤ = ⊤ := by
  cases n <;> rfl

def atom (n : Nat) (a : α) : Carrier α κ n :=
  match n with
  | 0 => literal a
  | _ + 1 => literal (.atom a)

def unary (n : Nat) (k : κ) (p : Carrier α κ n) : Carrier α κ n :=
  match n with
  | 0 => ⊥
  | n + 1 => literal (.unary k (project n p))

def binary (n : Nat) (k : κ) (p q : Carrier α κ n) : Carrier α κ n :=
  match n with
  | 0 => ⊥
  | n + 1 => literal (.binary k (project n p) (project n q))

/-- Interpret the entire syntax in an actual ortholattice at each finite depth. -/
def interpret (n : Nat) (t : Term α κ) : Carrier α κ n :=
  t.eval (atom n) (unary n) (binary n)

@[simp] theorem project_atom (n : Nat) (a : α) :
    project n (atom (κ := κ) (n + 1) a) = atom n a := by
  cases n <;> rfl

@[simp] theorem project_unary (n : Nat) (k : κ) (p : Carrier α κ (n + 1)) :
    project n (unary (n + 1) k p) = unary n k (project n p) := by
  cases n <;> rfl

@[simp] theorem project_binary (n : Nat) (k : κ) (p q : Carrier α κ (n + 1)) :
    project n (binary (n + 1) k p q) = binary n k (project n p) (project n q) := by
  cases n <;> rfl

@[simp] theorem project_interpret (t : Term α κ) (n : Nat) :
    project n (interpret (n + 1) t) = interpret n t := by
  induction t with
  | atom a => exact project_atom n a
  | bot => exact project_bot n
  | top => exact project_top n
  | meet p q ihp ihq => exact (project_inf n _ _).trans (congrArg₂ (· ⊓ ·) ihp ihq)
  | join p q ihp ihq => exact (project_sup n _ _).trans (congrArg₂ (· ⊔ ·) ihp ihq)
  | neg p ih => exact (project_compl n _).trans (congrArg Compl.compl ih)
  | unary k p ih => exact (project_unary n _ _).trans (congrArg (unary n k) ih)
  | binary k p q ihp ihq =>
      exact (project_binary n _ _ _).trans (congrArg₂ (binary n k) ihp ihq)

/-- Evaluate a finite carrier in any target algebra without choosing representatives. -/
def evaluate {L : Type} [Ortholattice L] (v : α → L)
    (u : κ → L → L) (b : κ → L → L → L) (n : Nat) : Carrier α κ n → L :=
  match n with
  | 0 => Free.lift v
  | n + 1 => Free.lift (fun
      | .atom a => v a
      | .unary k p => u k (evaluate v u b n p)
      | .binary k p q => b k (evaluate v u b n p) (evaluate v u b n q))

private theorem evaluate_mono {L : Type} [Ortholattice L] (v : α → L)
    (u : κ → L → L) (b : κ → L → L → L) (n : Nat) :
    Monotone (evaluate v u b n) := by
  cases n <;> exact lift_mono _

/-- Recover exact target evaluation once the layer covers all constructor nesting. -/
theorem evaluate_interpret {L : Type} [Ortholattice L] (v : α → L)
    (u : κ → L → L) (b : κ → L → L → L) (t : Term α κ) (n : Nat)
    (h : t.depth ≤ n) : evaluate v u b n (interpret n t) = t.eval v u b := by
  induction t generalizing n with
  | atom a => cases n <;> rfl
  | bot => cases n <;> rfl
  | top => cases n <;> rfl
  | meet p q ihp ihq =>
      have hp : p.depth ≤ n := (Nat.le_max_left _ _).trans h
      have hq : q.depth ≤ n := (Nat.le_max_right _ _).trans h
      cases n <;> simp only [interpret, Term.eval, evaluate, Free.lift_inf] <;>
        exact congrArg₂ (· ⊓ ·) (ihp _ hp) (ihq _ hq)
  | join p q ihp ihq =>
      have hp : p.depth ≤ n := (Nat.le_max_left _ _).trans h
      have hq : q.depth ≤ n := (Nat.le_max_right _ _).trans h
      cases n <;> simp only [interpret, Term.eval, evaluate, Free.lift_sup] <;>
        exact congrArg₂ (· ⊔ ·) (ihp _ hp) (ihq _ hq)
  | neg p ih =>
      cases n <;> simp only [interpret, Term.eval, evaluate, Free.lift_compl] <;>
        exact congrArg Compl.compl (ih _ h)
  | unary k p ih =>
      cases n with
      | zero => simp [Term.depth] at h
      | succ n =>
          change u k (evaluate v u b n (project n (interpret (n + 1) p))) = _
          rw [project_interpret, ih n (Nat.le_of_succ_le_succ h)]
          rfl
  | binary k p q ihp ihq =>
      cases n with
      | zero => simp [Term.depth] at h
      | succ n =>
          have hd : max p.depth q.depth ≤ n := Nat.le_of_succ_le_succ h
          change b k (evaluate v u b n (project n (interpret (n + 1) p)))
            (evaluate v u b n (project n (interpret (n + 1) q))) = _
          rw [project_interpret, project_interpret,
            ihp n ((Nat.le_max_left _ _).trans hd),
            ihq n ((Nat.le_max_right _ _).trans hd)]
          rfl

/-- Characterize all valid inequalities using one syntax-derived finite layer. -/
theorem interpret_valid (p q : Term α κ) (n : Nat)
    (hp : p.depth ≤ n) (hq : q.depth ≤ n) :
    interpret n p ≤ interpret n q ↔ ∀ (L : Type) [Ortholattice L] (v : α → L)
      (u : κ → L → L) (b : κ → L → L → L), p.eval v u b ≤ q.eval v u b := by
  constructor
  · intro h L _ v u b
    simpa only [evaluate_interpret v u b p n hp, evaluate_interpret v u b q n hq]
      using evaluate_mono v u b n h
  · intro h
    exact h (Carrier α κ n) (atom n) (unary n) (binary n)

/-- Keep the answer unchanged when increasing an already sufficient depth. -/
theorem interpret_stable (p q : Term α κ) (n m : Nat)
    (hpn : p.depth ≤ n) (hqn : q.depth ≤ n)
    (hpm : p.depth ≤ m) (hqm : q.depth ≤ m) :
    interpret n p ≤ interpret n q ↔ interpret m p ≤ interpret m q :=
  (interpret_valid p q n hpn hqn).trans (interpret_valid p q m hpm hqm).symm

private def labelsDecidableEq [DecidableEq α] [DecidableEq κ] :
    (n : Nat) → DecidableEq (Labels α κ n)
  | 0 => inferInstanceAs (DecidableEq α)
  | n + 1 =>
      letI : DecidableEq (Labels α κ n) := labelsDecidableEq n
      letI : DecidableEq (Free (Labels α κ n)) := Free.decEq
      inferInstanceAs (DecidableEq (Label α κ (Free (Labels α κ n))))

instance [DecidableEq α] [DecidableEq κ] (n : Nat) : DecidableEq (Labels α κ n) :=
  labelsDecidableEq n

/-- Capture the computed depth in atom equality instead of rescanning the inputs. -/
@[noinline] private def checkAt [DecidableEq α] [DecidableEq κ]
    (n : Nat) (p q : Term α κ) : Bool :=
  Free.compare (interpret n p) (interpret n q)

/-- Decide contextual OL by the exact maximum constructor depth of the input. -/
def check [DecidableEq α] [DecidableEq κ] (p q : Term α κ) : Bool :=
  if p = q then true
  else checkAt (max p.depth q.depth) p q

theorem check_valid [DecidableEq α] [DecidableEq κ] (p q : Term α κ) :
    check p q = true ↔ ∀ (L : Type) [Ortholattice L] (v : α → L)
      (u : κ → L → L) (b : κ → L → L → L), p.eval v u b ≤ q.eval v u b := by
  unfold check
  split
  · rename_i h
    subst q
    simp
  · rw [checkAt, Free.compare_iff]
    exact interpret_valid p q _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end Lisa.Orthologic.Contextual
