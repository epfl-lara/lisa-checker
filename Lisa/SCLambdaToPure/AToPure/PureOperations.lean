import Lisa.SCLambdaToPure.Pure

/-! Lifting substitution under binders, and recovering renaming and identity
as special cases of substitution. -/
namespace Lisa.SCLambdaToPure.Pure
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
    Substitution.lift (BTerm.var (L := L) ∘ ρ) = BTerm.var ∘ ρ.lift := by
  funext x
  cases x with
  | inl x => rfl
  | inr i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def, BTerm.rename]

mutual
  theorem BTerm.subst_ofRen {n m : Nat} :
      (t : BTerm L α n) → (ρ : Renaming α n β m) → t.subst (BTerm.var ∘ ρ) = t.rename ρ
    | .var _, ρ => rfl
    | .func f ts, ρ => congrArg (BTerm.func f) (funext fun i => BTerm.subst_ofRen (ts i) ρ)
    | .epsilon p, ρ => by
        simp only [BTerm.subst, BTerm.rename, Substitution.lift_ofRen]
        exact congrArg (BTerm.epsilon) (BFormula.subst_ofRen p ρ.lift)
  theorem BFormula.subst_ofRen {n m : Nat} :
      (p : BFormula L α n) → (ρ : Renaming α n β m) → p.subst (BTerm.var ∘ ρ) = p.rename ρ
    | .rel r ts, ρ => congrArg (BFormula.rel r) (funext fun i => BTerm.subst_ofRen (ts i) ρ)
    | .equal t u, ρ => congrArg₂ BFormula.equal (BTerm.subst_ofRen t ρ) (BTerm.subst_ofRen u ρ)
    | .top, ρ => rfl
    | .bot, ρ => rfl
    | .not p, ρ => by
        simp only [BFormula.subst, BFormula.rename]
        exact congrArg BFormula.not (BFormula.subst_ofRen p ρ)
    | .and p q, ρ => congrArg₂ BFormula.and (BFormula.subst_ofRen p ρ) (BFormula.subst_ofRen q ρ)
    | .or p q, ρ => congrArg₂ BFormula.or (BFormula.subst_ofRen p ρ) (BFormula.subst_ofRen q ρ)
    | .imp p q, ρ => congrArg₂ BFormula.imp (BFormula.subst_ofRen p ρ) (BFormula.subst_ofRen q ρ)
    | .iff p q, ρ => congrArg₂ BFormula.iff (BFormula.subst_ofRen p ρ) (BFormula.subst_ofRen q ρ)
    | .all p, ρ => by
        simp only [BFormula.subst, BFormula.rename, Substitution.lift_ofRen]
        exact congrArg BFormula.all (BFormula.subst_ofRen p ρ.lift)
    | .ex p, ρ => by
        simp only [BFormula.subst, BFormula.rename, Substitution.lift_ofRen]
        exact congrArg BFormula.ex (BFormula.subst_ofRen p ρ.lift)
end

@[simp] theorem BTerm.subst_id (t : BTerm L α n) :
    t.subst BTerm.var = t := by simpa using t.subst_ofRen id
@[simp] theorem BFormula.subst_id (p : BFormula L α n) :
    p.subst BTerm.var = p := by simpa using p.subst_ofRen id

end Lisa.SCLambdaToPure.Pure

/-! Free-variable support through first-order quantifiers and epsilon.
Bound slots stay separate from free names throughout substitution. -/
namespace Lisa.SCLambdaToPure.Pure
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
  theorem BTerm.mem_freeVars_rename {n m : Nat} :
      (t : BTerm L α n) → (ρ : Renaming α n β m) →
      (∀ i, ∃ j, ρ (.inr i) = .inr j) → (y : β) →
      (y ∈ (t.rename ρ).freeVars ↔ ∃ x ∈ t.freeVars, ρ (.inl x) = .inl y)
    | .var (.inl x), ρ, _, y => by
        cases hr : ρ (.inl x) <;> simp [BTerm.rename, BTerm.freeVars, hr, eq_comm]
    | .var (.inr i), ρ, hb, y => by
        obtain ⟨j, hj⟩ := hb i
        simp [BTerm.rename, BTerm.freeVars, hj]
    | .func f ts, ρ, hb, y => by
        simp only [BTerm.rename, BTerm.freeVars, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        simp only [BTerm.mem_freeVars_rename _ ρ hb y]
        exact exists_comm.trans (by simp only [exists_and_right])
    | .epsilon p, ρ, hb, y => by
        simpa only [BTerm.rename, BTerm.freeVars, lift_eq_free] using
          BFormula.mem_freeVars_rename p ρ.lift (lift_bound ρ hb) y
  theorem BFormula.mem_freeVars_rename {n m : Nat} :
      (p : BFormula L α n) → (ρ : Renaming α n β m) →
      (∀ i, ∃ j, ρ (.inr i) = .inr j) → (y : β) →
      (y ∈ (p.rename ρ).freeVars ↔ ∃ x ∈ p.freeVars, ρ (.inl x) = .inl y)
    | .rel r ts, ρ, hb, y => by
        simp only [BFormula.rename, BFormula.freeVars, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        simp only [BTerm.mem_freeVars_rename _ ρ hb y]
        exact exists_comm.trans (by simp only [exists_and_right])
    | .equal t u, ρ, hb, y => by
        simp only [BFormula.rename, BFormula.freeVars, Finset.mem_union,
          BTerm.mem_freeVars_rename t ρ hb y, BTerm.mem_freeVars_rename u ρ hb y]
        exact exists_or _ _ _
    | .top, ρ, hb, y | .bot, ρ, hb, y => by simp [BFormula.rename, BFormula.freeVars]
    | .not p, ρ, hb, y => BFormula.mem_freeVars_rename p ρ hb y
    | .and p q, ρ, hb, y | .or p q, ρ, hb, y | .imp p q, ρ, hb, y | .iff p q, ρ, hb, y => by
        simp only [BFormula.rename, BFormula.freeVars, Finset.mem_union,
          BFormula.mem_freeVars_rename p ρ hb y, BFormula.mem_freeVars_rename q ρ hb y]
        exact exists_or _ _ _
    | .all p, ρ, hb, y | .ex p, ρ, hb, y => by
        simpa only [BFormula.rename, BFormula.freeVars, lift_eq_free] using
          BFormula.mem_freeVars_rename p ρ.lift (lift_bound ρ hb) y
end

@[simp] theorem freeVars_bind (x : Identifier) (p : Formula L) :
    (bind x p).freeVars = p.freeVars.erase x := by
  ext y
  rw [bind, BFormula.mem_freeVars_rename _ _ (fun i => Fin.elim0 i)]
  simp [close, Finset.mem_erase]
  aesop

@[simp] theorem freeVars_forall (x : Identifier) (p : Formula L) :
    (forall_ x p).freeVars = p.freeVars.erase x := freeVars_bind x p
@[simp] theorem freeVars_exists (x : Identifier) (p : Formula L) :
    (exists_ x p).freeVars = p.freeVars.erase x := freeVars_bind x p
@[simp] theorem freeVars_epsilon (x : Identifier) (p : Formula L) :
    (epsilon_ x p).freeVars = p.freeVars.erase x := freeVars_bind x p

end Lisa.SCLambdaToPure.Pure

/-! Substitution depends only on the variables occurring in an expression. -/
namespace Lisa.SCLambdaToPure.Pure
open FirstOrder
variable {L : Language.{0, 0}} {α β : Type}

private theorem lift_agree_free (σ τ : Substitution L α n β m)
    (h : σ (.inl x) = τ (.inl x)) : σ.lift (.inl x) = τ.lift (.inl x) :=
  congrArg (BTerm.rename shift) h
private theorem lift_agree_bound (σ τ : Substitution L α n β m)
    (h : ∀ i, σ (.inr i) = τ (.inr i)) : ∀ i, σ.lift (.inr i) = τ.lift (.inr i) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Substitution.lift]
  · simp [Substitution.lift, h]

variable [DecidableEq α]

mutual
  theorem BTerm.subst_congr {n m : Nat} (t : BTerm L α n)
      (σ τ : Substitution L α n β m)
      (hf : ∀ x ∈ t.freeVars, σ (.inl x) = τ (.inl x))
      (hb : ∀ i, σ (.inr i) = τ (.inr i)) : t.subst σ = t.subst τ := by
    match t with
    | .var (.inl x) => exact hf x (by simp [BTerm.freeVars])
    | .var (.inr i) => exact hb i
    | .func f ts =>
        apply congrArg (BTerm.func f)
        funext i
        exact BTerm.subst_congr (ts i) σ τ
          (fun x hx => hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hb
    | .epsilon p =>
        apply congrArg (BTerm.epsilon)
        exact BFormula.subst_congr p σ.lift τ.lift
          (fun x hx => lift_agree_free σ τ (hf x hx)) (lift_agree_bound σ τ hb)
  theorem BFormula.subst_congr {n m : Nat} (p : BFormula L α n)
      (σ τ : Substitution L α n β m)
      (hf : ∀ x ∈ p.freeVars, σ (.inl x) = τ (.inl x))
      (hb : ∀ i, σ (.inr i) = τ (.inr i)) : p.subst σ = p.subst τ := by
    match p with
    | .rel r ts =>
        apply congrArg (BFormula.rel r)
        funext i
        exact BTerm.subst_congr (ts i) σ τ
          (fun x hx => hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)) hb
    | .equal t u =>
        exact congrArg₂ BFormula.equal
          (BTerm.subst_congr t σ τ (fun x hx => hf x (Finset.mem_union_left _ hx)) hb)
          (BTerm.subst_congr u σ τ (fun x hx => hf x (Finset.mem_union_right _ hx)) hb)
    | .top | .bot => rfl
    | .not p => exact congrArg BFormula.not (BFormula.subst_congr p σ τ hf hb)
    | .and p q | .or p q | .imp p q | .iff p q =>
        simp only [BFormula.subst]
        exact congrArg₂ _
          (BFormula.subst_congr p σ τ (fun x hx => hf x (Finset.mem_union_left _ hx)) hb)
          (BFormula.subst_congr q σ τ (fun x hx => hf x (Finset.mem_union_right _ hx)) hb)
    | .all p | .ex p =>
        simp only [BFormula.subst]
        exact congrArg _ (BFormula.subst_congr p σ.lift τ.lift
          (fun x hx => lift_agree_free σ τ (hf x hx)) (lift_agree_bound σ τ hb))
end

@[simp] theorem substOne_self (x : Identifier) (p : Formula L) :
    substOne x (.var (.inl x)) p = p := by
  have hs : single x (.var (.inl x)) = (BTerm.var : Substitution L Identifier 0 Identifier 0) := by
    funext z
    cases z with
    | inl y => by_cases h : y = x <;> simp [single, h]
    | inr i => exact Fin.elim0 i
  simp [substOne, hs]

theorem BTerm.subst_single_fresh (t u : Term L) (hx : x ∉ t.freeVars) :
    t.subst (single x u) = t := by
  apply Eq.trans (b := t.subst BTerm.var) _ t.subst_id
  apply BTerm.subst_congr
  · intro y hy
    have hn : y ≠ x := fun h => hx (h ▸ hy)
    simp [single, hn]
  · intro i; exact Fin.elim0 i

end Lisa.SCLambdaToPure.Pure
