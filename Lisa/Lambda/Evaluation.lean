import Lisa.Lambda.AlphaBetaEta
import Lisa.Lambda.Semantics

/-! Evaluation respects the syntactic operations. Functions use ordinary
extensionality; there is no semantic context transport. -/
namespace Lisa.Lambda

@[simp] theorem eval_bound (n : Nat) (η : Env) : eval (.bound (s := s) n) η = η s n := rfl

@[simp] theorem eval_free (x : Identifier) (η : Env) : eval (.free (s := s) x) η = reflect s (fun _ => .free x) := rfl

@[simp] theorem eval_const (c : Identifier) (η : Env) : eval (.const (s := s) c) η = reflect s (fun _ => .const c) := rfl

@[simp] theorem eval_app (f : Term (s >> t)) (a : Term s) (η : Env) : eval (.app f a) η = eval f η (eval a η) := rfl

@[simp] theorem eval_lam_apply (b : Term t) (η : Env) (a : Val s) : eval (.lam s b) η a = eval b (η.extend a) := rfl

theorem eval_rename (e : Term s) (ρ : Ren) (η : Env) :
    eval (e.rename ρ) η = eval e (fun s n => η s (ρ s n)) := by
  induction e generalizing ρ η with
  | lam b e ih =>
      funext a
      simp only [Term.rename, eval_lam_apply, ih]
      congr 1
      funext s n
      by_cases h : s = b
      · subst s; cases n <;> simp [Ren.lift, Env.extend]
      · simp [Ren.lift, Env.extend, h]
  | _ => simp_all [Term.rename, eval]

theorem eval_shift_extend (e : Term t) (η : Env) (a : Val s) :
    eval (e.shift s) (η.extend a) = eval e η := by
  rw [eval_rename]
  congr 1
  funext u n
  by_cases h : u = s <;> simp [Ren.shift, Env.extend, h]

theorem eval_subst (e : Term s) (σ : Sub) (η : Env) :
    eval (e.subst σ) η = eval e (fun s n => eval (σ s n) η) := by
  induction e generalizing σ η with
  | lam b e ih =>
      funext a
      simp only [Term.subst, eval_lam_apply, ih]
      congr 1
      funext s n
      by_cases h : s = b
      · subst s; cases n <;> simp [Sub.lift, Env.extend, eval_bound, eval_shift_extend]
      · simp [Sub.lift, Env.extend, h, eval_shift_extend]
  | _ => simp_all [Term.subst, eval]

theorem Equiv.eval_eq (h : Equiv e f) (η : Env) : eval e η = eval f η := by
  induction h generalizing η with
  | refl => rfl
  | symm _ ih => exact (ih η).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ η).trans (ih₂ η)
  | app _ _ ih₁ ih₂ => simp only [eval_app, ih₁ η, ih₂ η]
  | lam _ ih => funext a; exact ih _
  | @beta t s b a =>
      simp only [eval_app, eval_lam_apply, Term.instantiate, eval_subst]
      congr 1
      funext u n
      by_cases h : u = s
      · subst u; cases n <;> simp [Term.single, Sub.extend, Sub.id, Env.extend]
      · simp [Term.single, Sub.extend, Sub.id, Env.extend, h]
  | eta f =>
      funext a
      simp only [eval_lam_apply, eval_app, eval_bound, Env.extend_zero, eval_shift_extend]

theorem normalize_eq_of_equiv (h : Equiv e f) : normalize e = normalize f :=
  congrArg (quote _ Depth.zero) (h.eval_eq ambient)
end Lisa.Lambda
