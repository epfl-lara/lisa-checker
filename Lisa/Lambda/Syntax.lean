import Lisa.Sort

/-! Use intrinsically sorted de Bruijn terms for capture-free lambda metatheory. -/

namespace Lisa.Lambda

/-- Locate a variable in a sorted binder context. -/
inductive Var : List LSort → LSort → Type where
  | here : Var (s :: Γ) s
  | there : Var Γ s → Var (t :: Γ) s

/-- Separate free identifiers from bound indices and rule out malformed applications. -/
inductive Term : List LSort → LSort → Type where
  | bound : Var Γ s → Term Γ s
  | free (id : Identifier) : Term Γ s
  | const (id : Identifier) : Term Γ s
  | app : Term Γ (s >> t) → Term Γ s → Term Γ t
  | lam : Term (s :: Γ) t → Term Γ (s >> t)

abbrev Ren (Γ Δ : List LSort) := ∀ {s}, Var Γ s → Var Δ s

namespace Ren

def id : Ren Γ Γ := fun v => v

def comp (ρ : Ren Γ Δ) (τ : Ren Δ Θ) : Ren Γ Θ := fun v => τ (ρ v)

def lift (ρ : Ren Γ Δ) : Ren (s :: Γ) (s :: Δ)
  | _, .here => .here
  | _, .there v => .there (ρ v)

@[simp] theorem lift_here (ρ : Ren Γ Δ) : lift (s := s) ρ .here = .here := rfl

@[simp] theorem lift_there (ρ : Ren Γ Δ) (v : Var Γ t) :
    lift (s := s) ρ (.there v) = .there (ρ v) := rfl

@[simp] theorem lift_id : @lift Γ Γ s id = @id (s :: Γ) := by
  funext t v
  cases v <;> rfl

@[simp] theorem lift_comp (ρ : Ren Γ Δ) (τ : Ren Δ Θ) :
    @lift Γ Θ s (comp ρ τ) = @comp (s :: Γ) (s :: Δ) (s :: Θ) (lift ρ) (lift τ) := by
  funext t v
  cases v <;> rfl

end Ren

namespace Term

/-- Rename bound variables, lifting the map beneath each binder. -/
def rename (ρ : Ren Γ Δ) : Term Γ s → Term Δ s
  | .bound v => .bound (ρ v)
  | .free x => .free x
  | .const c => .const c
  | .app f a => .app (f.rename ρ) (a.rename ρ)
  | .lam b => .lam (b.rename (Ren.lift ρ))

@[simp] theorem rename_id (e : Term Γ s) : e.rename Ren.id = e := by
  induction e with
  | lam b ih => simp [rename, ih]
  | _ => simp_all [rename, Ren.id]

@[simp] theorem rename_comp (e : Term Γ s) (ρ : Ren Γ Δ) (τ : Ren Δ Θ) :
    (e.rename ρ).rename τ = e.rename (Ren.comp ρ τ) := by
  induction e generalizing Δ Θ with
  | lam b ih => simp [rename, ih]
  | _ => simp_all [rename, Ren.comp]

end Term

abbrev Sub (Γ Δ : List LSort) := ∀ {s}, Var Γ s → Term Δ s

namespace Sub

def id : Sub Γ Γ := fun v => .bound v

def ofRen (ρ : Ren Γ Δ) : Sub Γ Δ := fun v => .bound (ρ v)

def extend (σ : Sub Γ Δ) (a : Term Δ s) : Sub (s :: Γ) Δ
  | _, .here => a
  | _, .there v => σ v

/-- Keep the new binder fixed and weaken every existing replacement. -/
def lift (σ : Sub Γ Δ) : Sub (s :: Γ) (s :: Δ)
  | _, .here => .bound .here
  | _, .there v => (σ v).rename Var.there

@[simp] theorem lift_here (σ : Sub Γ Δ) :
    lift (s := s) σ .here = .bound .here := rfl

@[simp] theorem lift_there (σ : Sub Γ Δ) (v : Var Γ t) :
    lift (s := s) σ (.there v) = (σ v).rename Var.there := rfl

@[simp] theorem lift_id : @lift Γ Γ s id = @id (s :: Γ) := by
  funext t v
  cases v <;> rfl

@[simp] theorem lift_ofRen (ρ : Ren Γ Δ) :
    @lift Γ Δ s (ofRen ρ) = @ofRen (s :: Γ) (s :: Δ) (Ren.lift ρ) := by
  funext t v
  cases v <;> rfl

end Sub

namespace Term

/-- Substitute sorted terms simultaneously without fresh-name generation. -/
def subst (σ : Sub Γ Δ) : Term Γ s → Term Δ s
  | .bound v => σ v
  | .free x => .free x
  | .const c => .const c
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .lam b => .lam (b.subst (Sub.lift σ))

@[simp] theorem subst_id (e : Term Γ s) : e.subst Sub.id = e := by
  induction e with
  | lam b ih => simp [subst, ih]
  | _ => simp_all [subst, Sub.id]

@[simp] theorem subst_ofRen (e : Term Γ s) (ρ : Ren Γ Δ) :
    e.subst (Sub.ofRen ρ) = e.rename ρ := by
  induction e generalizing Δ with
  | lam b ih => simp [subst, rename, ih]
  | _ => simp_all [subst, rename, Sub.ofRen]

theorem rename_subst (e : Term Γ s) (σ : Sub Γ Δ) (ρ : Ren Δ Θ) :
    (e.subst σ).rename ρ = e.subst (fun v => (σ v).rename ρ) := by
  induction e generalizing Δ Θ with
  | lam b ih =>
      simp only [subst, rename, ih]
      congr 2
      funext t v
      cases v with
      | here => rfl
      | there v =>
          simp only [Sub.lift, rename_comp]
          rfl
  | _ => simp_all [subst, rename]

theorem subst_rename (e : Term Γ s) (ρ : Ren Γ Δ) (σ : Sub Δ Θ) :
    (e.rename ρ).subst σ = e.subst (fun v => σ (ρ v)) := by
  induction e generalizing Δ Θ with
  | lam b ih =>
      simp only [rename, subst, ih]
      congr 2
      funext t v
      cases v <;> rfl
  | _ => simp_all [subst, rename]

@[simp] theorem subst_comp (e : Term Γ s) (σ : Sub Γ Δ) (τ : Sub Δ Θ) :
    (e.subst σ).subst τ = e.subst (fun v => (σ v).subst τ) := by
  induction e generalizing Δ Θ with
  | lam b ih =>
      simp only [subst, ih]
      congr 2
      funext t v
      cases v with
      | here => rfl
      | there v =>
          simp only [Sub.lift, subst_rename, rename_subst]
  | _ => simp_all [subst]

/-- Substitute the argument for the innermost binder. -/
def single (arg : Term Γ s) : Sub (s :: Γ) Γ
  | _, .here => arg
  | _, .there w => .bound w

def instantiate (body : Term (s :: Γ) t) (arg : Term Γ s) : Term Γ t :=
  body.subst (single arg)

end Term

end Lisa.Lambda
