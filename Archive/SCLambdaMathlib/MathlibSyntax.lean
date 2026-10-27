import Lisa.SCLambdaToPure.PureBinding
import Lisa.SCLambdaToPure.Pure

/-! Compatibility with the epsilon-free Mathlib syntax used by the existing
A/B development. This is a syntactic bridge, independent of model theory and
completeness. Mathlib's encoded connectives remain encoded under `ofFormula`. -/
namespace Lisa.SCLambdaToPure.MathlibSyntax
open FirstOrder
open PureSyntax
variable {L : Language.{0, 0}} {α β : Type} {n : Nat}

def ofTerm : L.Term (α ⊕ Fin n) → BTerm L .fol α n
  | .var x => .var x
  | .func f ts => .func f (fun i => ofTerm (ts i))

def ofFormula {n : Nat} : L.BoundedFormula α n → BFormula L .fol α n
  | .falsum => .bot
  | .equal t u => .equal (ofTerm t) (ofTerm u)
  | .rel r ts => .rel r (fun i => ofTerm (ts i))
  | .imp p q => .imp (ofFormula p) (ofFormula q)
  | .all p => .all (ofFormula p)

def toTerm : BTerm L .fol α n → L.Term (α ⊕ Fin n)
  | .var x => .var x
  | .func f ts => .func f (fun i => toTerm (ts i))
  | .epsilon h _ => nomatch h

def toFormula {n : Nat} : BFormula L .fol α n → L.BoundedFormula α n
  | .rel r ts => .rel r (fun i => toTerm (ts i))
  | .equal t u => .equal (toTerm t) (toTerm u)
  | .top => ⊤
  | .bot => ⊥
  | .not p => (toFormula p).not
  | .and p q => toFormula p ⊓ toFormula q
  | .or p q => toFormula p ⊔ toFormula q
  | .imp p q => (toFormula p).imp (toFormula q)
  | .iff p q => (toFormula p).iff (toFormula q)
  | .all p => (toFormula p).all
  | .ex p => (toFormula p).ex

@[simp] theorem toTerm_ofTerm (t : L.Term (α ⊕ Fin n)) : toTerm (ofTerm t) = t := by
  induction t with
  | var => rfl
  | func f ts ih => exact congrArg (Language.Term.func f) (funext ih)

@[simp] theorem toFormula_ofFormula (p : L.BoundedFormula α n) : toFormula (ofFormula p) = p := by
  induction p with
  | falsum => rfl
  | equal t u => simp [ofFormula, toFormula]
  | rel r ts => simp [ofFormula, toFormula]
  | imp p q ih ih' => simp [ofFormula, toFormula, ih, ih']
  | all p ih => simp [ofFormula, toFormula, ih]

theorem ofTerm_relabel (t : L.Term (α ⊕ Fin n)) (ρ : Renaming α n β m) :
    ofTerm (t.relabel ρ) = (ofTerm t).rename ρ := by
  induction t with
  | var => rfl
  | func f ts ih => exact congrArg (BTerm.func f) (funext ih)

theorem ofTerm_subst (t : L.Term (α ⊕ Fin n)) (σ : α ⊕ Fin n → L.Term (β ⊕ Fin m)) :
    ofTerm (t.subst σ) = (ofTerm t).subst (fun x => ofTerm (σ x)) := by
  induction t with
  | var => rfl
  | func f ts ih => exact congrArg (BTerm.func f) (funext ih)

theorem toTerm_relabel {n m : Nat} : (t : BTerm L .fol α n) → (ρ : Renaming α n β m) →
    toTerm (t.rename ρ) = (toTerm t).relabel ρ
  | .var _, _ => rfl
  | .func f ts, ρ => congrArg (Language.Term.func f) (funext fun i => toTerm_relabel (ts i) ρ)
  | .epsilon h _, _ => nomatch h

theorem toTerm_subst {n m : Nat} : (t : BTerm L .fol α n) → (σ : Substitution L .fol α n β m) →
    toTerm (t.subst σ) = (toTerm t).subst (fun x => toTerm (σ x))
  | .var _, _ => rfl
  | .func f ts, σ => congrArg (Language.Term.func f) (funext fun i => toTerm_subst (ts i) σ)
  | .epsilon h _, _ => nomatch h

/-- Relabeling a Mathlib formula adds slots before its existing bound slots.
This is exactly the lifting convention of the independent syntax. -/
theorem relabelAux_lift (g : α → β ⊕ Fin m) (k : Nat) :
    Renaming.lift (Language.BoundedFormula.relabelAux g k) =
      Language.BoundedFormula.relabelAux g (k + 1) := by
  funext x
  cases x with
  | inl x =>
      cases h : g x <;> simp [Language.BoundedFormula.relabelAux, h, Renaming.lift, shift]
      rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Language.BoundedFormula.relabelAux, Renaming.lift]
      · simp [Language.BoundedFormula.relabelAux, Renaming.lift, shift]

theorem ofFormula_relabel (p : L.BoundedFormula α n) (g : α → β ⊕ Fin m) :
    ofFormula (p.relabel g) = (ofFormula p).rename (Language.BoundedFormula.relabelAux g n) := by
  induction p with
  | falsum => rfl
  | equal t u => simp [ofFormula, Language.BoundedFormula.relabel,
      Language.BoundedFormula.mapTermRel, BFormula.rename, ofTerm_relabel]
  | rel r ts => simp [ofFormula, Language.BoundedFormula.relabel,
      Language.BoundedFormula.mapTermRel, BFormula.rename, ofTerm_relabel]
  | imp p q ih ih' => simp [ofFormula, BFormula.rename, ih, ih']
  | all p ih => simpa [ofFormula, BFormula.rename, relabelAux_lift] using congrArg BFormula.all ih

def freeSub (σ : α → L.Term β) (n : Nat) : Substitution L .fol α n β n :=
  fun x => ofTerm (Sum.elim (fun a => (σ a).relabel Sum.inl) (fun i => .var (.inr i)) x)

theorem freeSub_lift (σ : α → L.Term β) (n : Nat) : (freeSub σ n).lift = freeSub σ (n + 1) := by
  funext x
  cases x with
  | inl x =>
      simp only [Substitution.lift_free, freeSub, Sum.elim_inl, ← ofTerm_relabel, Language.Term.relabel_relabel]
      rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [freeSub, ofTerm, Substitution.lift, BTerm.rename, shift]

theorem ofFormula_subst (p : L.BoundedFormula α n) (σ : α → L.Term β) :
    ofFormula (p.subst σ) = (ofFormula p).subst (freeSub σ n) := by
  induction p with
  | falsum => rfl
  | equal t u =>
      change BFormula.equal (ofTerm (t.subst _)) (ofTerm (u.subst _)) = _
      rw [ofTerm_subst, ofTerm_subst]
      rfl
  | rel r ts =>
      change BFormula.rel r (fun i => ofTerm ((ts i).subst _)) = _
      simp only [ofTerm_subst]
      rfl
  | imp p q ih ih' => exact congrArg₂ BFormula.imp ih ih'
  | all p ih =>
      change BFormula.all (ofFormula (p.subst σ)) = BFormula.all ((ofFormula p).subst (freeSub σ _).lift)
      rw [ih, freeSub_lift]

@[simp] theorem ofTerm_toTerm {n : Nat} : (t : BTerm L .fol α n) → ofTerm (toTerm t) = t
  | .var _ => rfl
  | .func f ts => congrArg (BTerm.func f) (funext fun i => ofTerm_toTerm (ts i))
  | .epsilon h _ => nomatch h

theorem toFormula_relabel {n : Nat} : (p : BFormula L .fol α n) → (g : α → β ⊕ Fin m) →
    toFormula (p.rename (Language.BoundedFormula.relabelAux g n)) = (toFormula p).relabel g
  | .rel r ts, g => by
      simp [BFormula.rename, toFormula, Language.BoundedFormula.relabel,
        Language.BoundedFormula.mapTermRel, toTerm_relabel]
  | .equal t u, g => by
      simp [BFormula.rename, toFormula, Language.BoundedFormula.relabel,
        Language.BoundedFormula.mapTermRel, toTerm_relabel]
  | .top, _ => rfl
  | .bot, _ => rfl
  | .not p, g => by simpa [BFormula.rename, toFormula] using congrArg Language.BoundedFormula.not (toFormula_relabel p g)
  | .and p q, g => by
      change _ = ((toFormula p).imp (toFormula q).not).not.relabel g
      simp only [BFormula.rename, toFormula, Language.BoundedFormula.relabel_not,
        Language.BoundedFormula.relabel_imp, toFormula_relabel]
      rfl
  | .or p q, g => by
      change _ = ((toFormula p).not.imp (toFormula q)).relabel g
      simp only [BFormula.rename, toFormula, Language.BoundedFormula.relabel_not,
        Language.BoundedFormula.relabel_imp, toFormula_relabel]
      rfl
  | .imp p q, g => by simp [BFormula.rename, toFormula, toFormula_relabel p g, toFormula_relabel q g]
  | .iff p q, g => by
      change _ = (((toFormula p).imp (toFormula q)).imp ((toFormula q).imp (toFormula p)).not).not.relabel g
      simp only [BFormula.rename, toFormula, Language.BoundedFormula.relabel_not,
        Language.BoundedFormula.relabel_imp, toFormula_relabel]
      rfl
  | .all p, g => by
      simpa [BFormula.rename, toFormula, relabelAux_lift] using congrArg Language.BoundedFormula.all (toFormula_relabel p g)
  | .ex p, g => by
      simpa [BFormula.rename, toFormula, relabelAux_lift] using congrArg Language.BoundedFormula.ex (toFormula_relabel p g)

theorem toFormula_subst {n : Nat} : (p : BFormula L .fol α n) → (σ : α → L.Term β) →
    toFormula (p.subst (freeSub σ n)) = (toFormula p).subst σ
  | .rel r ts, σ => by
      simp [BFormula.subst, toFormula, Language.BoundedFormula.subst,
        Language.BoundedFormula.mapTermRel, toTerm_subst, freeSub, Function.comp_def]
  | .equal t u, σ => by
      simp [BFormula.subst, toFormula, Language.BoundedFormula.subst,
        Language.BoundedFormula.mapTermRel, toTerm_subst, freeSub, Function.comp_def]
  | .top, _ => rfl
  | .bot, _ => rfl
  | .not p, σ => congrArg Language.BoundedFormula.not (toFormula_subst p σ)
  | .and p q, σ => congrArg₂ (fun p q => p ⊓ q) (toFormula_subst p σ) (toFormula_subst q σ)
  | .or p q, σ => congrArg₂ (fun p q => p ⊔ q) (toFormula_subst p σ) (toFormula_subst q σ)
  | .imp p q, σ => congrArg₂ Language.BoundedFormula.imp (toFormula_subst p σ) (toFormula_subst q σ)
  | .iff p q, σ => congrArg₂ Language.BoundedFormula.iff (toFormula_subst p σ) (toFormula_subst q σ)
  | .all p, σ => by
      change (toFormula (p.subst (freeSub σ _).lift)).all = ((toFormula p).subst σ).all
      rw [freeSub_lift, toFormula_subst]
  | .ex p, σ => by
      change (toFormula (p.subst (freeSub σ _).lift)).ex = ((toFormula p).subst σ).ex
      rw [freeSub_lift, toFormula_subst]

def ofFreeTerm (t : L.Term α) : BTerm L .fol α 0 := ofTerm (t.relabel Sum.inl)
def toFreeTerm (t : BTerm L .fol α 0) : L.Term α := (toTerm t).relabel (Sum.elim id Fin.elim0)

@[simp] theorem toFreeTerm_ofFreeTerm (t : L.Term α) : toFreeTerm (ofFreeTerm t) = t := by
  simp [toFreeTerm, ofFreeTerm, Language.Term.relabel_relabel]

@[simp] theorem ofFreeTerm_toFreeTerm (t : BTerm L .fol α 0) : ofFreeTerm (toFreeTerm t) = t := by
  have hh : Sum.inl ∘ (Sum.elim id Fin.elim0 : α ⊕ Fin 0 → α) = id := by
    funext x; cases x with
    | inl => rfl
    | inr i => exact Fin.elim0 i
  simp [toFreeTerm, ofFreeTerm, Language.Term.relabel_relabel, hh]

theorem close_eq (x : Nat) : close x = Language.BoundedFormula.relabelAux
    (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y) 0 := by
  funext z
  cases z with
  | inl y =>
      by_cases h : y = x <;> simp [close, Language.BoundedFormula.relabelAux, h]
      rfl
  | inr i => exact Fin.elim0 i

@[simp] theorem ofFormula_bind (x : Nat) (p : Pure.Formula L) :
    ofFormula (Pure.bind x p) = PureSyntax.bind x (ofFormula p) := by
  rw [Pure.bind, ofFormula_relabel, PureSyntax.bind, close_eq]

@[simp] theorem toFormula_bind (x : Nat) (p : PureSyntax.Formula L .fol) :
    toFormula (PureSyntax.bind x p) = Pure.bind x (toFormula p) := by
  rw [PureSyntax.bind, close_eq, toFormula_relabel, Pure.bind]

theorem freeSub_single (x : Nat) (t : L.Term Nat) :
    freeSub (fun y => if y = x then t else .var y) 0 = single x (ofFreeTerm t) := by
  funext z
  cases z with
  | inl y => by_cases h : y = x <;> simp [freeSub, single, h, ofFreeTerm, ofTerm]
  | inr i => exact Fin.elim0 i

@[simp] theorem ofFormula_substOne (x : Nat) (t : Pure.Term L) (p : Pure.Formula L) :
    ofFormula (Pure.substOne x t p) = PureSyntax.substOne x (ofFreeTerm t) (ofFormula p) := by
  rw [Pure.substOne, ofFormula_subst, freeSub_single, PureSyntax.substOne]

@[simp] theorem toFormula_substOne (x : Nat) (t : PureSyntax.Term L .fol) (p : PureSyntax.Formula L .fol) :
    toFormula (PureSyntax.substOne x t p) = Pure.substOne x (toFreeTerm t) (toFormula p) := by
  rw [PureSyntax.substOne, ← ofFreeTerm_toFreeTerm t, ← freeSub_single, toFormula_subst]
  simp [Pure.substOne]

theorem toTerm_freeVars [DecidableEq α] {n : Nat} : (t : BTerm L .fol α n) →
    (toTerm t).varFinsetLeft = t.freeVars
  | .var (.inl _) => by simp [toTerm, BTerm.freeVars]
  | .var (.inr _) => by simp [toTerm, BTerm.freeVars]
  | .func f ts => by simp [toTerm, BTerm.freeVars, Language.Term.varFinsetLeft, toTerm_freeVars]
  | .epsilon h _ => nomatch h

theorem toFormula_freeVars [DecidableEq α] {n : Nat} : (p : BFormula L .fol α n) →
    (toFormula p).freeVarFinset = p.freeVars
  | .rel r ts => by simp [toFormula, BFormula.freeVars, toTerm_freeVars]
  | .equal t u => by simp [toFormula, BFormula.freeVars, toTerm_freeVars]
  | .top => rfl
  | .bot => rfl
  | .not p => by simp [toFormula, Language.BoundedFormula.not, BFormula.freeVars, toFormula_freeVars p]
  | .and p q => by
      change (((toFormula p).imp (toFormula q).not).not).freeVarFinset = _
      simp [BFormula.freeVars, toFormula_freeVars p, toFormula_freeVars q]
  | .or p q => by
      change ((toFormula p).not.imp (toFormula q)).freeVarFinset = _
      simp [BFormula.freeVars, toFormula_freeVars p, toFormula_freeVars q]
  | .imp p q => by simp [toFormula, BFormula.freeVars, toFormula_freeVars p, toFormula_freeVars q]
  | .iff p q => by
      change (((toFormula p).imp (toFormula q)).imp ((toFormula q).imp (toFormula p)).not).not.freeVarFinset = _
      simp [BFormula.freeVars, toFormula_freeVars p, toFormula_freeVars q,
        Finset.union_comm]
  | .all p => by simpa [toFormula, BFormula.freeVars] using toFormula_freeVars p
  | .ex p => by simpa [toFormula, Language.BoundedFormula.ex, Language.BoundedFormula.not, BFormula.freeVars] using toFormula_freeVars p

theorem ofFormula_freeVars [DecidableEq α] (p : L.BoundedFormula α n) :
    (ofFormula p).freeVars = p.freeVarFinset := by
  rw [← toFormula_freeVars, toFormula_ofFormula]

end Lisa.SCLambdaToPure.MathlibSyntax
