import Lisa.Lambda.Syntax

/-! The independently specified beta-eta relation and its substitution laws. -/
namespace Lisa.Lambda
namespace Term

@[simp] theorem shift_instantiate (e : Term t) (a : Term s) : (e.shift s).instantiate a = e := by
  simp only [instantiate, subst_rename]
  have h : (fun t n => single a t (Ren.shift s t n)) = Sub.id := by
    funext t n
    by_cases h : t = s <;> simp [single, Sub.extend, Ren.shift, Sub.id, h]
  rw [h, subst_id]

theorem instantiate_rename (b : Term t) (a : Term s) (ρ : Ren) :
    (b.instantiate a).rename ρ = (b.rename (ρ.lift s)).instantiate (a.rename ρ) := by
  simp only [instantiate, rename_subst, subst_rename]
  congr 1
  funext u n
  by_cases h : u = s
  · subst u; cases n <;> simp [single, Sub.extend, Sub.id, rename, Ren.lift]
  · simp [single, Sub.extend, rename, Ren.lift, h, Sub.id]

theorem instantiate_subst (b : Term t) (σ : Sub) (a : Term s) :
    (b.subst (σ.lift s)).instantiate a = b.subst (Sub.extend σ a) := by
  simp only [instantiate, subst_comp]
  congr 1
  funext u n
  by_cases h : u = s
  · subst u; cases n with
    | zero => simp [Sub.lift, subst, single]
    | succ n => simpa only [Sub.lift_succ, Sub.extend_succ] using (σ s n).shift_instantiate a
  · simpa only [Sub.lift_other h, Sub.extend_other h] using (σ u n).shift_instantiate a
end Term

/-- Beta-eta conversion, specified independently of evaluation. -/

inductive Equiv : Term s → Term s → Prop
  | refl (e) : Equiv e e
  | symm : Equiv e f → Equiv f e
  | trans : Equiv e f → Equiv f g → Equiv e g
  | app : Equiv f g → Equiv a b → Equiv (.app f a) (.app g b)
  | lam : Equiv b c → Equiv (.lam s b) (.lam s c)
  | beta (b : Term t) (a : Term s) : Equiv (.app (.lam s b) a) (b.instantiate a)
  | eta (f : Term (s >> t)) : Equiv (.lam s (.app (f.shift s) (.bound 0))) f

namespace Equiv

@[refl] theorem reflexive (e : Term s) : Equiv e e := .refl e

theorem rename (h : Equiv e f) (ρ : Ren) : Equiv (e.rename ρ) (f.rename ρ) := by
  induction h generalizing ρ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | lam _ ih => exact .lam (ih (ρ.lift _))
  | beta b a => simpa only [Term.rename, Term.instantiate_rename] using beta (b.rename (ρ.lift _)) (a.rename ρ)
  | eta f => simpa [Term.rename, Ren.lift_shift] using eta (f.rename ρ)
end Equiv

theorem Term.instantiate_subst_comp (b : Term t) (a : Term s) (σ : Sub) :
    (b.instantiate a).subst σ = (b.subst (σ.lift s)).instantiate (a.subst σ) := by
  rw [instantiate_subst]
  simp only [instantiate, subst_comp]
  congr 1
  funext u n
  by_cases h : u = s
  · subst u; cases n <;> simp [single, Sub.extend, Sub.id, subst]
  · simp [single, Sub.extend, Sub.id, subst, h]

theorem Equiv.subst (h : Equiv e f) (σ : Sub) : Equiv (e.subst σ) (f.subst σ) := by
  induction h generalizing σ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ σ) (ih₂ σ)
  | lam _ ih => exact .lam (ih (σ.lift _))
  | beta b a => simpa only [Term.subst, Term.instantiate_subst_comp] using Equiv.beta (b.subst (σ.lift _)) (a.subst σ)
  | @eta s t f =>
      have hs : (fun u n => σ.lift s u (Ren.shift s u n)) = (fun u n => (σ u n).shift s) := by
        funext u n
        by_cases h : u = s <;> simp [Sub.lift, Ren.shift, h]
      simpa [Term.subst, Term.subst_rename, Term.rename_subst, hs] using Equiv.eta (f.subst σ)
end Lisa.Lambda
