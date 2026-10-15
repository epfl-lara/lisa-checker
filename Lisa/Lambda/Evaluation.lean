import Lisa.Lambda.Conversion
import Lisa.Lambda.Semantics

/-! Preserve typed conversion through evaluation and readback. -/

namespace Lisa.Lambda

@[simp] theorem eval_bound (v : Var Γ s) (η : Env Γ Δ) :
    eval (.bound v) η = η v := rfl

@[simp] theorem eval_free (x : Identifier) (η : Env Γ Δ) :
    eval (.free (s := s) x) η = (model s).reflect (.free x) := rfl

@[simp] theorem eval_const (c : Identifier) (η : Env Γ Δ) :
    eval (.const (s := s) c) η = (model s).reflect (.const c) := rfl

@[simp] theorem eval_app (f : Term Γ (s >> t)) (a : Term Γ s) (η : Env Γ Δ) :
    eval (.app f a) η = (eval f η).run Ren.id (eval a η) := rfl

@[simp] theorem eval_lam_run (b : Term (s :: Γ) t) (η : Env Γ Δ)
    (ρ : Ren Δ Θ) (a : Val Θ s) :
    (eval (.lam b) η).run ρ a = eval b (Env.extend (Env.rename η ρ) a) := rfl

theorem eval_rename (e : Term Γ s) (ρ : Ren Γ Δ) (η : Env Δ Θ) :
    eval (e.rename ρ) η = eval e (fun v => η (ρ v)) := by
  induction e generalizing Δ Θ with
  | bound => rfl
  | free => rfl
  | const => rfl
  | app f a ihf iha => simp only [Term.rename, eval_app, ihf, iha]
  | lam b ih =>
      apply Family.Fn.ext
      intro Ξ τ a
      simp only [Term.rename, eval_lam_run, ih]
      congr 1
      funext u v
      cases v <;> rfl

theorem eval_subst (e : Term Γ s) (σ : Sub Γ Δ) (η : Env Δ Θ) :
    eval (e.subst σ) η = eval e (fun v => eval (σ v) η) := by
  induction e generalizing Δ Θ with
  | bound => rfl
  | free => rfl
  | const => rfl
  | app f a ihf iha => simp only [Term.subst, eval_app, ihf, iha]
  | lam b ih =>
      apply Family.Fn.ext
      intro Ξ τ a
      simp only [Term.subst, eval_lam_run, ih]
      congr 1
      funext u v
      cases v with
      | here => rfl
      | there v =>
          simp only [Sub.lift, eval_rename]
          exact (eval_natural (σ v) η τ).symm

/-- Interpret every beta-eta conversion by equality in the lawful Kripke model. -/
theorem Equiv.eval_eq {e f : Term Γ s} (h : Equiv e f) (η : Env Γ Δ) :
    eval e η = eval f η := by
  induction h generalizing Δ with
  | refl => rfl
  | symm _ ih => exact (ih η).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ η).trans (ih₂ η)
  | app _ _ ih₁ ih₂ => simp only [eval_app, ih₁ η, ih₂ η]
  | lam _ ih =>
      apply Family.Fn.ext
      intro Θ ρ a
      exact ih _
  | beta b a =>
      simp only [eval_app, eval_lam_run, Env.rename_id, Term.instantiate, eval_subst]
      congr 1
      funext u v
      cases v <;> rfl
  | eta f =>
      apply Family.Fn.ext
      intro Θ ρ a
      simp only [eval_lam_run, eval_app, eval_bound, eval_rename]
      change (eval f (Env.rename η ρ)).run Ren.id a = (eval f η).run ρ a
      rw [← eval_natural]
      rfl

/-- Give conversion-invariant readback without a fuel or termination hypothesis. -/
theorem normalize_eq_of_equiv {e f : Term Γ s} (h : Equiv e f) :
    normalize e = normalize f := congrArg (model s).quote (h.eval_eq _)


end Lisa.Lambda
