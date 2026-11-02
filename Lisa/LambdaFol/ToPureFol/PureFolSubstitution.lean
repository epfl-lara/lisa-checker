import Lisa.LambdaFol.PureFol

/-! Lifting substitution under binders, and recovering renaming and identity
as special cases of substitution. -/
namespace Lisa.LambdaFol.PureFol
open FirstOrder
variable {L : Language.{0, 0}} {α β γ : Type} {n m k : Nat}

@[simp] theorem Substitution.lift_free (σ : Substitution L α n β m) (x : α) :
    σ.lift (.inl x) = (σ (.inl x)).rename shift := rfl
@[simp] theorem Substitution.lift_last (σ : Substitution L α n β m) :
    σ.lift (.inr (Fin.last n)) = .var (.inr (Fin.last m)) := by simp [lift]
@[simp] theorem Substitution.lift_castSucc (σ : Substitution L α n β m) (i : Fin n) :
    σ.lift (.inr i.castSucc) = (σ (.inr i)).rename shift := by simp [lift]

theorem Substitution.lift_shift (σ : Substitution L α n β m) (x : α ⊕ Fin n) :
    σ.lift (shift x) = (σ x).rename shift := by cases x <;> simp [shift]

theorem Substitution.lift_ofRen (ρ : Renaming α n β m) :
    Substitution.lift (BoundedTerm.var (L := L) ∘ ρ) = BoundedTerm.var ∘ ρ.lift := by
  funext x
  cases x with
  | inl x => rfl
  | inr i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def, BoundedTerm.rename]

-- Substitution by variables is renaming, including under all three binders.
mutual
  theorem BoundedTerm.subst_ofRen {n m : Nat} (t : BoundedTerm L α n) (ρ : Renaming α n β m) :
      t.subst (BoundedTerm.var ∘ ρ) = t.rename ρ := by
    match t with
    | .var _ => rfl
    | .func f ts => exact congrArg (BoundedTerm.func f) (funext fun i => BoundedTerm.subst_ofRen (ts i) ρ)
    | .epsilon p =>
        simp only [BoundedTerm.subst, BoundedTerm.rename, Substitution.lift_ofRen, BoundedFormula.subst_ofRen]
  theorem BoundedFormula.subst_ofRen {n m : Nat} (p : BoundedFormula L α n) (ρ : Renaming α n β m) :
      p.subst (BoundedTerm.var ∘ ρ) = p.rename ρ := by
    match p with
    | .rel r ts => exact congrArg (BoundedFormula.rel r) (funext fun i => BoundedTerm.subst_ofRen (ts i) ρ)
    | .equal t u => exact congrArg₂ BoundedFormula.equal (BoundedTerm.subst_ofRen t ρ) (BoundedTerm.subst_ofRen u ρ)
    | .top | .bot => rfl
    | .not p => simp only [BoundedFormula.subst, BoundedFormula.rename, BoundedFormula.subst_ofRen]
    | .and p q | .or p q | .imp p q | .iff p q =>
        simp only [BoundedFormula.subst, BoundedFormula.rename, BoundedFormula.subst_ofRen]
    | .all p | .ex p =>
        simp only [BoundedFormula.subst, BoundedFormula.rename, Substitution.lift_ofRen, BoundedFormula.subst_ofRen]
end

@[simp] theorem BoundedTerm.subst_id (t : BoundedTerm L α n) :
    t.subst BoundedTerm.var = t := by simpa using t.subst_ofRen id
@[simp] theorem BoundedFormula.subst_id (p : BoundedFormula L α n) :
    p.subst BoundedTerm.var = p := by simpa using p.subst_ofRen id

end Lisa.LambdaFol.PureFol

/-! Free-variable support through first-order quantifiers and epsilon.
Bound slots stay separate from free names throughout substitution. -/
namespace Lisa.LambdaFol.PureFol
open FirstOrder
variable {L : Language.{0, 0}} {α β : Type}

private theorem shift_eq_free (z : β ⊕ Fin m) (y : β) :
    shift z = .inl y ↔ z = .inl y := by cases z <;> simp [shift]

private theorem lift_eq_free (ρ : Renaming α n β m) (x : α) (y : β) :
    ρ.lift (.inl x) = .inl y ↔ ρ (.inl x) = .inl y := shift_eq_free _ _

private theorem lift_bound (ρ : Renaming α n β m)
    (hb : ∀ i, ∃ j, ρ (.inr i) = .inr j) :
    ∀ i, ∃ j, ρ.lift (.inr i) = .inr j := by
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · exact ⟨Fin.last m, by simp⟩
  · obtain ⟨j, hj⟩ := hb k
    exact ⟨j.castSucc, by simp [hj, shift]⟩

private theorem exists_or (P Q R : α → Prop) :
    ((∃ x, P x ∧ R x) ∨ (∃ x, Q x ∧ R x)) ↔
      ∃ x, (P x ∨ Q x) ∧ R x := by
  simp only [or_and_right, _root_.exists_or]

variable [DecidableEq α] [DecidableEq β]

mutual
  theorem BoundedTerm.mem_freeVars_rename {n m : Nat} :
      (t : BoundedTerm L α n) → (ρ : Renaming α n β m) →
      (∀ i, ∃ j, ρ (.inr i) = .inr j) → (y : β) →
      (y ∈ (t.rename ρ).freeVars ↔ ∃ x ∈ t.freeVars, ρ (.inl x) = .inl y)
    | .var (.inl x), ρ, _, y => by
        cases hr : ρ (.inl x) <;> simp [BoundedTerm.rename, BoundedTerm.freeVars, hr, eq_comm]
    | .var (.inr i), ρ, hb, y => by
        obtain ⟨j, hj⟩ := hb i
        simp [BoundedTerm.rename, BoundedTerm.freeVars, hj]
    | .func f ts, ρ, hb, y => by
        simp only [BoundedTerm.rename, BoundedTerm.freeVars, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        simp only [BoundedTerm.mem_freeVars_rename _ ρ hb y]
        exact exists_comm.trans (by simp only [exists_and_right])
    | .epsilon p, ρ, hb, y => by
        simpa only [BoundedTerm.rename, BoundedTerm.freeVars, lift_eq_free] using
          BoundedFormula.mem_freeVars_rename p ρ.lift (lift_bound ρ hb) y
  theorem BoundedFormula.mem_freeVars_rename {n m : Nat} :
      (p : BoundedFormula L α n) → (ρ : Renaming α n β m) →
      (∀ i, ∃ j, ρ (.inr i) = .inr j) → (y : β) →
      (y ∈ (p.rename ρ).freeVars ↔ ∃ x ∈ p.freeVars, ρ (.inl x) = .inl y)
    | .rel r ts, ρ, hb, y => by
        simp only [BoundedFormula.rename, BoundedFormula.freeVars, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        simp only [BoundedTerm.mem_freeVars_rename _ ρ hb y]
        exact exists_comm.trans (by simp only [exists_and_right])
    | .equal t u, ρ, hb, y => by
        simp only [BoundedFormula.rename, BoundedFormula.freeVars, Finset.mem_union,
          BoundedTerm.mem_freeVars_rename t ρ hb y, BoundedTerm.mem_freeVars_rename u ρ hb y]
        exact exists_or _ _ _
    | .top, ρ, hb, y | .bot, ρ, hb, y => by simp [BoundedFormula.rename, BoundedFormula.freeVars]
    | .not p, ρ, hb, y => BoundedFormula.mem_freeVars_rename p ρ hb y
    | .and p q, ρ, hb, y | .or p q, ρ, hb, y | .imp p q, ρ, hb, y | .iff p q, ρ, hb, y => by
        simp only [BoundedFormula.rename, BoundedFormula.freeVars, Finset.mem_union,
          BoundedFormula.mem_freeVars_rename p ρ hb y, BoundedFormula.mem_freeVars_rename q ρ hb y]
        exact exists_or _ _ _
    | .all p, ρ, hb, y | .ex p, ρ, hb, y => by
        simpa only [BoundedFormula.rename, BoundedFormula.freeVars, lift_eq_free] using
          BoundedFormula.mem_freeVars_rename p ρ.lift (lift_bound ρ hb) y
end

@[simp] theorem freeVars_bind (x : Identifier) (p : Formula L) :
    (bind x p).freeVars = p.freeVars.erase x := by
  ext y
  rw [bind, BoundedFormula.mem_freeVars_rename _ _ (fun i => Fin.elim0 i)]
  simp [close, Finset.mem_erase]
  aesop

@[simp] theorem freeVars_forall (x : Identifier) (p : Formula L) :
    (forall_ x p).freeVars = p.freeVars.erase x := freeVars_bind x p
@[simp] theorem freeVars_exists (x : Identifier) (p : Formula L) :
    (exists_ x p).freeVars = p.freeVars.erase x := freeVars_bind x p
@[simp] theorem freeVars_epsilon (x : Identifier) (p : Formula L) :
    (epsilon_ x p).freeVars = p.freeVars.erase x := freeVars_bind x p

end Lisa.LambdaFol.PureFol

/-! Substitution depends only on the variables occurring in an expression. -/
namespace Lisa.LambdaFol.PureFol
open FirstOrder
variable {L : Language.{0, 0}} {α β : Type}

private theorem lift_agree_free (σ τ : Substitution L α n β m)
    (h : σ (.inl x) = τ (.inl x)) : σ.lift (.inl x) = τ.lift (.inl x) :=
  congrArg (BoundedTerm.rename shift) h
private theorem lift_agree_bound (σ τ : Substitution L α n β m)
    (h : ∀ i, σ (.inr i) = τ (.inr i)) : ∀ i, σ.lift (.inr i) = τ.lift (.inr i) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Substitution.lift]
  · simp [Substitution.lift, h]

variable [DecidableEq α]

mutual
  theorem BoundedTerm.subst_congr {n m : Nat} (t : BoundedTerm L α n)
      (σ τ : Substitution L α n β m)
      (hf : ∀ x ∈ t.freeVars, σ (.inl x) = τ (.inl x))
      (hb : ∀ i, σ (.inr i) = τ (.inr i)) : t.subst σ = t.subst τ := by
    match t with
    | .var (.inl x) => exact hf x (by simp [BoundedTerm.freeVars])
    | .var (.inr i) => exact hb i
    | .func f ts =>
        apply congrArg (BoundedTerm.func f)
        funext i
        exact BoundedTerm.subst_congr (ts i) σ τ
          (fun x hx => hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hb
    | .epsilon p =>
        apply congrArg (BoundedTerm.epsilon)
        exact BoundedFormula.subst_congr p σ.lift τ.lift
          (fun x hx => lift_agree_free σ τ (hf x hx)) (lift_agree_bound σ τ hb)
  theorem BoundedFormula.subst_congr {n m : Nat} (p : BoundedFormula L α n)
      (σ τ : Substitution L α n β m)
      (hf : ∀ x ∈ p.freeVars, σ (.inl x) = τ (.inl x))
      (hb : ∀ i, σ (.inr i) = τ (.inr i)) : p.subst σ = p.subst τ := by
    match p with
    | .rel r ts =>
        apply congrArg (BoundedFormula.rel r)
        funext i
        exact BoundedTerm.subst_congr (ts i) σ τ
          (fun x hx => hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hb
    | .equal t u =>
        exact congrArg₂ BoundedFormula.equal
          (BoundedTerm.subst_congr t σ τ (fun x hx => hf x (Finset.mem_union_left _ hx)) hb)
          (BoundedTerm.subst_congr u σ τ (fun x hx => hf x (Finset.mem_union_right _ hx)) hb)
    | .top | .bot => rfl
    | .not p => exact congrArg BoundedFormula.not (BoundedFormula.subst_congr p σ τ hf hb)
    | .and p q | .or p q | .imp p q | .iff p q =>
        simp only [BoundedFormula.subst]
        exact congrArg₂ _
          (BoundedFormula.subst_congr p σ τ (fun x hx => hf x (Finset.mem_union_left _ hx)) hb)
          (BoundedFormula.subst_congr q σ τ (fun x hx => hf x (Finset.mem_union_right _ hx)) hb)
    | .all p | .ex p =>
        simp only [BoundedFormula.subst]
        exact congrArg _ (BoundedFormula.subst_congr p σ.lift τ.lift
          (fun x hx => lift_agree_free σ τ (hf x hx)) (lift_agree_bound σ τ hb))
end

@[simp] theorem substOne_self (x : Identifier) (p : Formula L) :
    substOne x (.var (.inl x)) p = p := by
  have hs : single x (.var (.inl x)) = (BoundedTerm.var : Substitution L Identifier 0 Identifier 0) := by
    funext z
    cases z with
    | inl y => by_cases h : y = x <;> simp [single, h]
    | inr i => exact Fin.elim0 i
  simp [substOne, hs]

theorem BoundedTerm.subst_single_fresh (t u : Term L) (hx : x ∉ t.freeVars) :
    t.subst (single x u) = t := by
  apply Eq.trans (b := t.subst BoundedTerm.var) _ t.subst_id
  apply BoundedTerm.subst_congr
  · intro y hy
    have hn : y ≠ x := fun h => hx (h ▸ hy)
    simp [single, hn]
  · intro i; exact Fin.elim0 i

end Lisa.LambdaFol.PureFol
