import Lisa.Sort

/-! Intrinsically sorted terms. Each sort has its own sequence of bound indices;
indices beyond local binders denote ambient variables of that sort. -/
namespace Lisa.Lambda

inductive Term : LSort → Type where
  | bound (index : Nat) : Term s
  | free (id : Identifier) : Term s
  | const (id : Identifier) : Term s
  | app : Term (s >> t) → Term s → Term t
  | lam (domain : LSort) : Term t → Term (domain >> t)
  deriving DecidableEq

abbrev Ren := LSort → Nat → Nat
namespace Ren

def id : Ren := fun _ n => n

def comp (ρ τ : Ren) : Ren := fun s n => τ s (ρ s n)

def shift (b : LSort) : Ren := fun s n => if s = b then n + 1 else n

def lift (b : LSort) (ρ : Ren) : Ren := fun s n =>
  if s = b then match n with
    | 0 => 0
    | n+1 => ρ s n + 1
  else ρ s n

@[simp] theorem lift_zero (ρ : Ren) : lift b ρ b 0 = 0 := by simp [lift]

@[simp] theorem lift_succ (ρ : Ren) : lift b ρ b (n+1) = ρ b n + 1 := by simp [lift]

@[simp] theorem lift_other (h : s ≠ b) (ρ : Ren) : lift b ρ s n = ρ s n := by simp [lift, h]

@[simp] theorem lift_id : lift b id = id := by
  funext s n
  by_cases h : s = b <;> cases n <;> simp [lift, id, h]

@[simp] theorem lift_comp (ρ τ : Ren) : lift b (comp ρ τ) = comp (lift b ρ) (lift b τ) := by
  funext s n
  by_cases h : s = b <;> cases n <;> simp [lift, comp, h]

theorem lift_shift (ρ : Ren) : comp (shift b) (lift b ρ) = comp ρ (shift b) := by
  funext s n
  by_cases h : s = b <;> simp [comp, shift, lift, h]
end Ren

namespace Term

def rename (ρ : Ren) : Term s → Term s
  | .bound n => .bound (ρ s n)
  | .free x => .free x
  | .const c => .const c
  | .app f a => .app (f.rename ρ) (a.rename ρ)
  | .lam b e => .lam b (e.rename (ρ.lift b))

abbrev shift (b : LSort) (e : Term s) := e.rename (Ren.shift b)

@[simp] theorem rename_id (e : Term s) : e.rename Ren.id = e := by
  induction e with
  | lam b e ih => simp [rename, ih]
  | _ => simp_all [rename, Ren.id]

@[simp] theorem rename_comp (e : Term s) (ρ τ : Ren) :
    (e.rename ρ).rename τ = e.rename (Ren.comp ρ τ) := by
  induction e generalizing ρ τ with
  | lam b e ih => simp [rename, ih]
  | _ => simp_all [rename, Ren.comp]
end Term

abbrev Sub := (s : LSort) → Nat → Term s
namespace Sub

def id : Sub := fun _ n => .bound n

def ofRen (ρ : Ren) : Sub := fun s n => .bound (ρ s n)

def extend (σ : Sub) (a : Term b) : Sub := fun s n =>
  if h : s = b then match n with
    | 0 => h.symm ▸ a
    | n+1 => σ s n
  else σ s n
/-- Replacement terms shift even when their result sort differs from the binder. -/

def lift (b : LSort) (σ : Sub) : Sub := fun s n =>
  if s = b then match n with
    | 0 => .bound 0
    | n+1 => (σ s n).shift b
  else (σ s n).shift b

@[simp] theorem extend_zero (σ : Sub) (a : Term b) : extend σ a b 0 = a := by simp [extend]

@[simp] theorem extend_succ (σ : Sub) (a : Term b) : extend σ a b (n+1) = σ b n := by simp [extend]

@[simp] theorem extend_other (h : s ≠ b) (σ : Sub) (a : Term b) : extend σ a s n = σ s n := by simp [extend, h]

@[simp] theorem lift_zero (σ : Sub) : lift b σ b 0 = .bound 0 := by simp [lift]

@[simp] theorem lift_succ (σ : Sub) : lift b σ b (n+1) = (σ b n).shift b := by simp [lift]

@[simp] theorem lift_other (h : s ≠ b) (σ : Sub) : lift b σ s n = (σ s n).shift b := by simp [lift, h]

@[simp] theorem lift_id : lift b id = id := by
  funext s n
  by_cases h : s = b <;> cases n <;> simp [lift, id, Term.rename, Ren.shift, h]

@[simp] theorem lift_ofRen (ρ : Ren) : lift b (ofRen ρ) = ofRen (ρ.lift b) := by
  funext s n
  by_cases h : s = b <;> cases n <;>
    simp [lift, ofRen, Term.rename, Ren.shift, Ren.lift, h]
end Sub

namespace Term

def subst (σ : Sub) : Term s → Term s
  | .bound n => σ s n
  | .free x => .free x
  | .const c => .const c
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .lam b e => .lam b (e.subst (σ.lift b))

@[simp] theorem subst_id (e : Term s) : e.subst Sub.id = e := by
  induction e with
  | lam b e ih => simp [subst, ih]
  | _ => simp_all [subst, Sub.id]

@[simp] theorem subst_ofRen (e : Term s) (ρ : Ren) : e.subst (Sub.ofRen ρ) = e.rename ρ := by
  induction e generalizing ρ with
  | lam b e ih => simp [subst, rename, ih]
  | _ => simp_all [subst, rename, Sub.ofRen]

theorem rename_subst (e : Term s) (σ : Sub) (ρ : Ren) :
    (e.subst σ).rename ρ = e.subst (fun s n => (σ s n).rename ρ) := by
  induction e generalizing σ ρ with
  | lam b e ih =>
      simp only [subst, rename, ih]
      congr 2
      funext s n
      by_cases h : s = b
      · subst s; cases n <;> simp [Sub.lift, rename, Ren.lift, Ren.lift_shift]
      · simp [Sub.lift, h, Ren.lift_shift]
  | _ => simp_all [subst, rename]

theorem subst_rename (e : Term s) (ρ : Ren) (σ : Sub) :
    (e.rename ρ).subst σ = e.subst (fun s n => σ s (ρ s n)) := by
  induction e generalizing σ ρ with
  | lam b e ih =>
      simp only [rename, subst, ih]
      congr 2
      funext s n
      by_cases h : s = b
      · subst s; cases n <;> simp [Sub.lift, Ren.lift]
      · simp [Sub.lift, Ren.lift, h]
  | _ => simp_all [subst, rename]

@[simp] theorem subst_comp (e : Term s) (σ τ : Sub) :
    (e.subst σ).subst τ = e.subst (fun s n => (σ s n).subst τ) := by
  induction e generalizing σ τ with
  | lam b e ih =>
      simp only [subst, ih]
      congr 2
      funext s n
      have hs (t : LSort) (k : Nat) : τ.lift b t (Ren.shift b t k) = (τ t k).shift b := by
        by_cases h : t = b <;> simp [Sub.lift, Ren.shift, h]
      by_cases h : s = b
      · subst s
        cases n with
        | zero => simp [Sub.lift, subst]
        | succ n => simp only [Sub.lift_succ, subst_rename, rename_subst, hs]
      · simp only [Sub.lift_other h, subst_rename, rename_subst, hs]
  | _ => simp_all [subst]

def single (a : Term b) : Sub := Sub.extend Sub.id a

def instantiate (e : Term t) (a : Term b) : Term t := e.subst (single a)
end Term
namespace Packed

abbrev Expr  := Σ s, Term s

def app : Expr → Expr → Option (Expr)
  | ⟨.arrow s t, f⟩, ⟨u, a⟩ =>
      if h : u = s then some ⟨t, .app f (h ▸ a)⟩ else none
  | _, _ => none

def lam (s : LSort) : Expr → Expr
  | ⟨t, b⟩ => ⟨s >> t, .lam s b⟩

def rename (ρ : Ren) : Expr → Expr
  | ⟨s, e⟩ => ⟨s, e.rename ρ⟩

def subst (σ : Sub) : Expr → Expr
  | ⟨s, e⟩ => ⟨s, e.subst σ⟩

theorem rename_app (ρ : Ren) (f a : Expr) :
    (app f a).map (rename ρ) = app (rename ρ f) (rename ρ a) := by
  rcases f with ⟨s, f⟩
  rcases a with ⟨u, a⟩
  cases s with
  | arrow s t =>
      by_cases h : u = s
      · subst u; simp [app, rename, Term.rename]
      · simp [app, rename, h]
  | _ => rfl

theorem subst_app (σ : Sub) (f a : Expr) :
    (app f a).map (subst σ) = app (subst σ f) (subst σ a) := by
  rcases f with ⟨s, f⟩
  rcases a with ⟨u, a⟩
  cases s with
  | arrow s t =>
      by_cases h : u = s
      · subst u; simp [app, subst, Term.subst]
      · simp [app, subst, h]
  | _ => rfl

end Packed
end Lisa.Lambda
