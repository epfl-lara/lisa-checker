import Lisa.Lambda.Syntax

namespace Lisa.Lambda

namespace Term

@[simp] theorem shift_instantiate (e : Term Γ t) (a : Term Γ s) :
    (e.rename Var.there).instantiate a = e := by
  simp only [instantiate, subst_rename]
  exact e.subst_id

theorem instantiate_rename (b : Term (s :: Γ) t) (a : Term Γ s) (ρ : Ren Γ Δ) :
    (b.instantiate a).rename ρ = (b.rename (Ren.lift ρ)).instantiate (a.rename ρ) := by
  simp only [instantiate, rename_subst, subst_rename]
  congr 1
  funext u v
  cases v <;> rfl

theorem instantiate_subst (b : Term (s :: Γ) t) (σ : Sub Γ Δ) (a : Term Δ s) :
    (b.subst (Sub.lift σ)).instantiate a = b.subst (Sub.extend σ a) := by
  simp only [instantiate, subst_comp]
  congr 1
  funext u v
  cases v with
  | here => rfl
  | there v => exact (σ v).shift_instantiate a

end Term

/-- Generate beta-eta equivalence on sorted, scoped terms; alpha is structural. -/
inductive Equiv : Term Γ s → Term Γ s → Prop
  | refl (e) : Equiv e e
  | symm {e f} : Equiv e f → Equiv f e
  | trans {e f g} : Equiv e f → Equiv f g → Equiv e g
  | app {f g : Term Γ (s >> t)} {a b : Term Γ s} :
      Equiv f g → Equiv a b → Equiv (.app f a) (.app g b)
  | lam {b c : Term (s :: Γ) t} : Equiv b c → Equiv (.lam b) (.lam c)
  | beta (b : Term (s :: Γ) t) (a : Term Γ s) :
      Equiv (.app (.lam b) a) (b.instantiate a)
  | eta (f : Term Γ (s >> t)) :
      Equiv (.lam (.app (f.rename Var.there) (.bound .here))) f

namespace Equiv

@[refl] theorem reflexive (e : Term Γ s) : Equiv e e := .refl e

theorem rename {e f : Term Γ s} (h : Equiv e f) (ρ : Ren Γ Δ) :
    Equiv (e.rename ρ) (f.rename ρ) := by
  induction h generalizing Δ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | lam _ ih => exact .lam (ih (Ren.lift ρ))
  | beta b a =>
      simpa only [Term.rename, Term.instantiate_rename] using
        beta (b.rename (Ren.lift ρ)) (a.rename ρ)
  | eta f =>
      simpa only [Term.rename, Term.rename_comp] using eta (f.rename ρ)

end Equiv

theorem Term.instantiate_subst_comp (b : Term (s :: Γ) t) (a : Term Γ s)
    (σ : Sub Γ Δ) :
    (b.instantiate a).subst σ = (b.subst (Sub.lift σ)).instantiate (a.subst σ) := by
  rw [Term.instantiate_subst]
  simp only [Term.instantiate, Term.subst_comp]
  congr 1
  funext u v
  cases v <;> rfl

/-- Preserve beta-eta equivalence under every sorted simultaneous substitution. -/
theorem Equiv.subst {e f : Term Γ s} (h : Equiv e f) (σ : Sub Γ Δ) :
    Equiv (e.subst σ) (f.subst σ) := by
  induction h generalizing Δ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ σ) (ih₂ σ)
  | lam _ ih => exact .lam (ih (Sub.lift σ))
  | beta b a =>
      simpa only [Term.subst, Term.instantiate_subst_comp] using
        Equiv.beta (b.subst (Sub.lift σ)) (a.subst σ)
  | eta f =>
      simpa only [Term.subst, Term.subst_rename, Term.rename_subst] using
        Equiv.eta (f.subst σ)

end Lisa.Lambda
