import Lisa.Sort
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Finset.Union

/-! Independent first-order syntax. Terms and formulas recurse through epsilon.
All binders bind individuals; bound variables use levels, with a new last slot.
-/

namespace Lisa.SCLambdaToPure.Pure

open FirstOrder

instance identifierInfinite : Infinite Identifier :=
  Infinite.of_injective (fun n : Nat => (⟨"", n⟩ : Identifier))
    (fun _ _ h => congrArg Identifier.idx h)

variable (L : Language.{0, 0}) (α : Type)

mutual
  inductive BTerm : Nat → Type where
    | var : α ⊕ Fin n → BTerm n
    | func : L.Functions k → (Fin k → BTerm n) → BTerm n
    | epsilon : BFormula (n + 1) → BTerm n
  inductive BFormula : Nat → Type where
    | rel : L.Relations k → (Fin k → BTerm n) → BFormula n
    | equal : BTerm n → BTerm n → BFormula n
    | top : BFormula n
    | bot : BFormula n
    | not : BFormula n → BFormula n
    | and : BFormula n → BFormula n → BFormula n
    | or : BFormula n → BFormula n → BFormula n
    | imp : BFormula n → BFormula n → BFormula n
    | iff : BFormula n → BFormula n → BFormula n
    | all : BFormula (n + 1) → BFormula n
    | ex : BFormula (n + 1) → BFormula n
end

abbrev Term := BTerm L Identifier 0
abbrev Formula := BFormula L Identifier 0
abbrev Context := Finset (Formula L)

variable {L α} {β γ : Type} {n m k : Nat}

abbrev Renaming (α : Type) (n : Nat) (β : Type) (m : Nat) :=
  α ⊕ Fin n → β ⊕ Fin m

def shift : Renaming α n α (n + 1) := Sum.map id Fin.castSucc

def Renaming.lift (ρ : Renaming α n β m) : Renaming α (n + 1) β (m + 1)
  | .inl x => shift (ρ (.inl x))
  | .inr i => Fin.lastCases (.inr (Fin.last m)) (fun j => shift (ρ (.inr j))) i

@[simp] theorem Renaming.lift_free (ρ : Renaming α n β m) (x : α) :
    ρ.lift (.inl x) = shift (ρ (.inl x)) := rfl
@[simp] theorem Renaming.lift_last (ρ : Renaming α n β m) :
    ρ.lift (.inr (Fin.last n)) = .inr (Fin.last m) := by simp [lift]
@[simp] theorem Renaming.lift_castSucc (ρ : Renaming α n β m) (i : Fin n) :
    ρ.lift (.inr i.castSucc) = shift (ρ (.inr i)) := by simp [lift]

theorem Renaming.lift_id : Renaming.lift (id : Renaming α n α n) = id := by
  funext x
  cases x with
  | inl x => rfl
  | inr i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [shift]

theorem Renaming.lift_shift (ρ : Renaming α n β m) (x : α ⊕ Fin n) :
    ρ.lift (shift x) = shift (ρ x) := by cases x <;> simp [shift]

theorem Renaming.lift_comp (ρ : Renaming α n β m) (τ : Renaming β m γ k) :
    Renaming.lift (τ ∘ ρ) = τ.lift ∘ ρ.lift := by
  funext x
  cases x with
  | inl x => simp [Function.comp_def, lift_shift]
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def, lift_shift]

mutual
  def BTerm.rename {n m : Nat} (ρ : Renaming α n β m) : BTerm L α n → BTerm L β m
    | .var x => .var (ρ x)
    | .func f ts => .func f (fun i => (ts i).rename ρ)
    | .epsilon p => .epsilon (p.rename ρ.lift)
  def BFormula.rename {n m : Nat} (ρ : Renaming α n β m) : BFormula L α n → BFormula L β m
    | .rel r ts => .rel r (fun i => (ts i).rename ρ)
    | .equal t u => .equal (t.rename ρ) (u.rename ρ)
    | .top => .top
    | .bot => .bot
    | .not p => .not (p.rename ρ)
    | .and p q => .and (p.rename ρ) (q.rename ρ)
    | .or p q => .or (p.rename ρ) (q.rename ρ)
    | .imp p q => .imp (p.rename ρ) (q.rename ρ)
    | .iff p q => .iff (p.rename ρ) (q.rename ρ)
    | .all p => .all (p.rename ρ.lift)
    | .ex p => .ex (p.rename ρ.lift)
end

mutual
  @[simp] theorem BTerm.rename_id {n : Nat} : (t : BTerm L α n) → t.rename id = t
    | .var _ => rfl
    | .func f ts => congrArg (BTerm.func f) (funext fun i => BTerm.rename_id (ts i))
    | .epsilon p => by
        simp only [BTerm.rename, Renaming.lift_id]
        exact congrArg (BTerm.epsilon) (BFormula.rename_id p)
  @[simp] theorem BFormula.rename_id {n : Nat} : (p : BFormula L α n) → p.rename id = p
    | .rel r ts => congrArg (BFormula.rel r) (funext fun i => BTerm.rename_id (ts i))
    | .equal t u => congrArg₂ BFormula.equal (BTerm.rename_id t) (BTerm.rename_id u)
    | .top => rfl
    | .bot => rfl
    | .not p => by
        simp only [BFormula.rename]
        exact congrArg BFormula.not (BFormula.rename_id p)
    | .and p q => congrArg₂ BFormula.and (BFormula.rename_id p) (BFormula.rename_id q)
    | .or p q => congrArg₂ BFormula.or (BFormula.rename_id p) (BFormula.rename_id q)
    | .imp p q => congrArg₂ BFormula.imp (BFormula.rename_id p) (BFormula.rename_id q)
    | .iff p q => congrArg₂ BFormula.iff (BFormula.rename_id p) (BFormula.rename_id q)
    | .all p => by
        simp only [BFormula.rename, Renaming.lift_id]
        exact congrArg BFormula.all (BFormula.rename_id p)
    | .ex p => by
        simp only [BFormula.rename, Renaming.lift_id]
        exact congrArg BFormula.ex (BFormula.rename_id p)
end

mutual
  theorem BTerm.rename_comp {n m k : Nat} :
      (t : BTerm L α n) → (ρ : Renaming α n β m) → (τ : Renaming β m γ k) →
      (t.rename ρ).rename τ = t.rename (τ ∘ ρ)
    | .var _, _, _ => rfl
    | .func f ts, ρ, τ => congrArg (BTerm.func f) (funext fun i => BTerm.rename_comp (ts i) ρ τ)
    | .epsilon p, ρ, τ => by
        simp only [BTerm.rename, Renaming.lift_comp]
        exact congrArg (BTerm.epsilon) (BFormula.rename_comp p ρ.lift τ.lift)
  theorem BFormula.rename_comp {n m k : Nat} :
      (p : BFormula L α n) → (ρ : Renaming α n β m) → (τ : Renaming β m γ k) →
      (p.rename ρ).rename τ = p.rename (τ ∘ ρ)
    | .rel r ts, ρ, τ => congrArg (BFormula.rel r) (funext fun i => BTerm.rename_comp (ts i) ρ τ)
    | .equal t u, ρ, τ => congrArg₂ BFormula.equal (BTerm.rename_comp t ρ τ) (BTerm.rename_comp u ρ τ)
    | .top, _, _ => rfl
    | .bot, _, _ => rfl
    | .not p, ρ, τ => by
        simp only [BFormula.rename]
        exact congrArg BFormula.not (BFormula.rename_comp p ρ τ)
    | .and p q, ρ, τ => congrArg₂ BFormula.and (BFormula.rename_comp p ρ τ) (BFormula.rename_comp q ρ τ)
    | .or p q, ρ, τ => congrArg₂ BFormula.or (BFormula.rename_comp p ρ τ) (BFormula.rename_comp q ρ τ)
    | .imp p q, ρ, τ => congrArg₂ BFormula.imp (BFormula.rename_comp p ρ τ) (BFormula.rename_comp q ρ τ)
    | .iff p q, ρ, τ => congrArg₂ BFormula.iff (BFormula.rename_comp p ρ τ) (BFormula.rename_comp q ρ τ)
    | .all p, ρ, τ => by
        simp only [BFormula.rename, Renaming.lift_comp]
        exact congrArg BFormula.all (BFormula.rename_comp p ρ.lift τ.lift)
    | .ex p, ρ, τ => by
        simp only [BFormula.rename, Renaming.lift_comp]
        exact congrArg BFormula.ex (BFormula.rename_comp p ρ.lift τ.lift)
end

abbrev Substitution (L : Language.{0, 0})
    (α : Type) (n : Nat) (β : Type) (m : Nat) :=
  α ⊕ Fin n → BTerm L β m

def Substitution.lift (σ : Substitution L α n β m) :
    Substitution L α (n + 1) β (m + 1)
  | .inl x => (σ (.inl x)).rename shift
  | .inr i => Fin.lastCases (.var (.inr (Fin.last m)))
      (fun j => (σ (.inr j)).rename shift) i

mutual
  def BTerm.subst {n m : Nat} (σ : Substitution L α n β m) : BTerm L α n → BTerm L β m
    | .var x => σ x
    | .func f ts => .func f (fun i => (ts i).subst σ)
    | .epsilon p => .epsilon (p.subst σ.lift)
  def BFormula.subst {n m : Nat} (σ : Substitution L α n β m) : BFormula L α n → BFormula L β m
    | .rel r ts => .rel r (fun i => (ts i).subst σ)
    | .equal t u => .equal (t.subst σ) (u.subst σ)
    | .top => .top
    | .bot => .bot
    | .not p => .not (p.subst σ)
    | .and p q => .and (p.subst σ) (q.subst σ)
    | .or p q => .or (p.subst σ) (q.subst σ)
    | .imp p q => .imp (p.subst σ) (q.subst σ)
    | .iff p q => .iff (p.subst σ) (q.subst σ)
    | .all p => .all (p.subst σ.lift)
    | .ex p => .ex (p.subst σ.lift)
end

def close (x : Identifier) : Renaming Identifier 0 Identifier 1
  | .inl y => if y = x then .inr 0 else .inl y
  | .inr i => Fin.elim0 i

def bind (x : Identifier) (p : Formula L) : BFormula L Identifier 1 := p.rename (close x)
def forall_ (x : Identifier) (p : Formula L) : Formula L := .all (bind x p)
def exists_ (x : Identifier) (p : Formula L) : Formula L := .ex (bind x p)
def epsilon_ (x : Identifier) (p : Formula L) : Term L :=
  .epsilon (bind x p)

def single (x : Identifier) (t : Term L) : Substitution L Identifier 0 Identifier 0
  | .inl y => if y = x then t else .var (.inl y)
  | .inr i => Fin.elim0 i

def substOne (x : Identifier) (t : Term L) (p : Formula L) : Formula L :=
  p.subst (single x t)

mutual
  def BTerm.freeVars [DecidableEq α] {n : Nat} : BTerm L α n → Finset α
    | .var (.inl x) => {x}
    | .var (.inr _) => ∅
    | .func _ ts => Finset.univ.biUnion (fun i => (ts i).freeVars)
    | .epsilon p => p.freeVars
  def BFormula.freeVars [DecidableEq α] {n : Nat} : BFormula L α n → Finset α
    | .rel _ ts => Finset.univ.biUnion (fun i => (ts i).freeVars)
    | .equal t u => t.freeVars ∪ u.freeVars
    | .top | .bot => ∅
    | .not p => p.freeVars
    | .and p q | .or p q | .imp p q | .iff p q => p.freeVars ∪ q.freeVars
    | .all p | .ex p => p.freeVars
end

def Fresh (x : Identifier) (Γ : Context L) : Prop := ∀ p ∈ Γ, x ∉ p.freeVars

end Lisa.SCLambdaToPure.Pure

/-! An independent first-order sequent calculus with epsilon.
All logical connectives are explicit syntax. The calculus includes witness
selection and contextual epsilon extensionality,
but no higher-order equality or schematic instantiation.
-/

namespace Lisa.SCLambdaToPure.Pure

open FirstOrder
variable {L : Language.{0, 0}}
variable [DecidableEq (Formula L)]

inductive ProofTree : Context L → Context L → Type where
  | hypothesis (p : Formula L) : ProofTree {p} {p}
  | weakening {Γ Δ Γ' Δ'} : ProofTree Γ Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → ProofTree Γ' Δ'
  | cut {Γ Δ Θ Ξ} (p : Formula L) :
      ProofTree Γ (insert p Δ) → ProofTree (insert p Θ) Ξ → ProofTree (Γ ∪ Θ) (Δ ∪ Ξ)
  | leftFalse : ProofTree {.bot} ∅
  | rightTrue : ProofTree ∅ {.top}
  | leftAnd {Γ Δ} (p q : Formula L) :
      ProofTree (insert p (insert q Γ)) Δ → ProofTree (insert (.and p q) Γ) Δ
  | rightAnd {Γ Δ Θ Ξ} (p q : Formula L) :
      ProofTree Γ (insert p Δ) → ProofTree Θ (insert q Ξ) →
      ProofTree (Γ ∪ Θ) (insert (.and p q) (Δ ∪ Ξ))
  | leftOr {Γ Δ Θ Ξ} (p q : Formula L) :
      ProofTree (insert p Γ) Δ → ProofTree (insert q Θ) Ξ →
      ProofTree (insert (.or p q) (Γ ∪ Θ)) (Δ ∪ Ξ)
  | rightOr {Γ Δ} (p q : Formula L) :
      ProofTree Γ (insert p (insert q Δ)) → ProofTree Γ (insert (.or p q) Δ)
  | leftImp {Γ Δ Θ Ξ} (p q : Formula L) :
      ProofTree Γ (insert p Δ) → ProofTree (insert q Θ) Ξ →
      ProofTree (insert (.imp p q) (Γ ∪ Θ)) (Δ ∪ Ξ)
  | rightImp {Γ Δ} (p q : Formula L) :
      ProofTree (insert p Γ) (insert q Δ) → ProofTree Γ (insert (.imp p q) Δ)
  | leftIff {Γ Δ} (p q : Formula L) :
      ProofTree (insert (.imp p q) (insert (.imp q p) Γ)) Δ →
      ProofTree (insert (.iff p q) Γ) Δ
  | rightIff {Γ Δ Θ Ξ} (p q : Formula L) :
      ProofTree Γ (insert (.imp p q) Δ) → ProofTree Θ (insert (.imp q p) Ξ) →
      ProofTree (Γ ∪ Θ) (insert (.iff p q) (Δ ∪ Ξ))
  | leftNot {Γ Δ} (p : Formula L) :
      ProofTree Γ (insert p Δ) → ProofTree (insert (.not p) Γ) Δ
  | rightNot {Γ Δ} (p : Formula L) :
      ProofTree (insert p Γ) Δ → ProofTree Γ (insert (.not p) Δ)
  | leftForall {Γ Δ} (x : Identifier) (p : Formula L) (t : Term L) :
      ProofTree (insert (substOne x t p) Γ) Δ → ProofTree (insert (forall_ x p) Γ) Δ
  | rightForall {Γ Δ} (x : Identifier) (p : Formula L) :
      ProofTree Γ (insert p Δ) → Fresh x Γ → Fresh x Δ →
      ProofTree Γ (insert (forall_ x p) Δ)
  | leftExists {Γ Δ} (x : Identifier) (p : Formula L) :
      ProofTree (insert p Γ) Δ → Fresh x Γ → Fresh x Δ →
      ProofTree (insert (exists_ x p) Γ) Δ
  | rightExists {Γ Δ} (x : Identifier) (p : Formula L) (t : Term L) :
      ProofTree Γ (insert (substOne x t p) Δ) → ProofTree Γ (insert (exists_ x p) Δ)
  | refl (t : Term L) : ProofTree ∅ {.equal t t}
  | leftSubst {Γ Δ Θ Ξ} (x : Identifier) (p : Formula L) (t u : Term L) :
      ProofTree (insert (substOne x t p) Γ) Δ → ProofTree Θ (insert (.equal t u) Ξ) →
      ProofTree (insert (substOne x u p) (Γ ∪ Θ)) (Δ ∪ Ξ)
  | rightSubst {Γ Δ Θ Ξ} (x : Identifier) (p : Formula L) (t u : Term L) :
      ProofTree Γ (insert (substOne x t p) Δ) → ProofTree Θ (insert (.equal t u) Ξ) →
      ProofTree (Γ ∪ Θ) (insert (substOne x u p) (Δ ∪ Ξ))
  | epsilonWitness {Γ Δ} (x : Identifier) (p : Formula L)
      (t : Term L) :
      ProofTree Γ (insert (substOne x t p) Δ) →
      ProofTree Γ (insert (substOne x (epsilon_ x p) p) Δ)
  | epsilonExt {Γ Δ} (x : Identifier) (p q : Formula L) :
      ProofTree Γ (insert (.iff p q) Δ) → Fresh x Γ → Fresh x Δ →
      ProofTree Γ (insert (.equal (epsilon_ x p) (epsilon_ x q)) Δ)

def Provable (Γ Δ : Context L) : Prop := Nonempty (ProofTree Γ Δ)

namespace ProofTree
variable {Γ Δ : Context L}

def hypothesisIn (p : Formula L) (hΓ : p ∈ Γ) (hΔ : p ∈ Δ) : ProofTree Γ Δ :=
  .weakening (.hypothesis p) (Finset.singleton_subset_iff.mpr hΓ)
    (Finset.singleton_subset_iff.mpr hΔ)

def leftRefl (t : Term L) (d : ProofTree (insert (.equal t t) Γ) Δ) :
    ProofTree Γ Δ := by
  simpa using ProofTree.cut (Γ := ∅) (Δ := ∅) (.equal t t) (.refl t) d

end ProofTree
end Lisa.SCLambdaToPure.Pure
