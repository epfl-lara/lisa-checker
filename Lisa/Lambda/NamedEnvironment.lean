import Lisa.Lambda.Elaboration
import Lisa.Lambda.Substitution

/-! Interpret named syntax in sorted environments before comparing substitutions. -/

namespace Lisa.Lambda

abbrev Names (Γ : List LSort) := (x : SVar) → Term Γ x.sort

namespace Names

def free : Names Γ := fun x => .free x.id

def rename (η : Names Γ) (ρ : Ren Γ Δ) : Names Δ := fun x => (η x).rename ρ

def subst (η : Names Γ) (σ : Sub Γ Δ) : Names Δ := fun x => (η x).subst σ

/-- Bind the selected name and weaken every other interpretation. -/
def bind (η : Names Γ) (x : SVar) : Names (x.sort :: Γ) := fun y =>
  if h : y = x then h.symm ▸ (Term.bound Var.here : Term (x.sort :: Γ) x.sort)
  else (η y).rename Var.there

@[simp] theorem bind_self (η : Names Γ) (x : SVar) : η.bind x x = .bound .here := by
  simp [bind]

@[simp] theorem bind_other (η : Names Γ) (h : y ≠ x) :
    η.bind x y = (η y).rename Var.there := by
  simp [bind, h]

theorem bind_rename (η : Names Γ) (ρ : Ren Γ Δ) (x : SVar) :
    (η.rename ρ).bind x = (η.bind x).rename (Ren.lift ρ) := by
  funext y
  by_cases h : y = x
  · subst y; simp [rename, Term.rename]
  · simp only [bind_other _ h, rename, Term.rename_comp]
    rfl

theorem bind_subst (η : Names Γ) (σ : Sub Γ Δ) (x : SVar) :
    (η.subst σ).bind x = (η.bind x).subst (Sub.lift σ) := by
  funext y
  by_cases h : y = x
  · subst y; simp [subst, Term.subst]
  · simp only [bind_other _ h, subst, Term.rename_subst, Term.subst_rename]
    rfl

end Names

namespace Packed

abbrev Expr (Γ : List LSort) := Σ s, Term Γ s

def app : Expr Γ → Expr Γ → Option (Expr Γ)
  | ⟨.arrow s t, f⟩, ⟨u, a⟩ =>
      if h : u = s then some ⟨t, .app f (h ▸ a)⟩ else none
  | _, _ => none

def lam (s : LSort) : Expr (s :: Γ) → Expr Γ
  | ⟨t, b⟩ => ⟨s >> t, .lam b⟩

def rename (ρ : Ren Γ Δ) : Expr Γ → Expr Δ
  | ⟨s, e⟩ => ⟨s, e.rename ρ⟩

def subst (σ : Sub Γ Δ) : Expr Γ → Expr Δ
  | ⟨s, e⟩ => ⟨s, e.subst σ⟩

theorem rename_app (ρ : Ren Γ Δ) (f a : Expr Γ) :
    (app f a).map (rename ρ) = app (rename ρ f) (rename ρ a) := by
  rcases f with ⟨s, f⟩
  rcases a with ⟨u, a⟩
  cases s with
  | arrow s t =>
      by_cases h : u = s
      · subst u; simp [app, rename, Term.rename]
      · simp [app, rename, h]
  | _ => rfl

theorem subst_app (σ : Sub Γ Δ) (f a : Expr Γ) :
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

/-- Resolve binders and free names while rejecting precisely ill-sorted applications. -/
def interpretNamed : (e : Expr) → Names Γ → Option (Packed.Expr Γ)
  | .var x, η => some ⟨x.sort, η x⟩
  | .const c, _ => some ⟨c.sort, .const c.id⟩
  | .app f a, η => do
      let f' ← interpretNamed f η
      let a' ← interpretNamed a η
      Packed.app f' a'
  | .lam x b, η => (interpretNamed b (η.bind x)).map (Packed.lam x.sort)

/-- Ignore environment entries outside the expression's free variables. -/
theorem interpretNamed_support (e : Expr) (η θ : Names Γ)
    (h : ∀ x ∈ e.freeVars, η x = θ x) : interpretNamed e η = interpretNamed e θ := by
  induction e generalizing Γ with
  | var x => simp [interpretNamed, h x (by simp)]
  | const => rfl
  | app f a ihf iha =>
      rw [interpretNamed, ihf η θ (fun x hx => h x (by simp [hx])),
        iha η θ (fun x hx => h x (by simp [hx]))]
      rfl
  | lam x b ih =>
      unfold interpretNamed
      congr 1
      apply ih
      intro y hy
      by_cases hyx : y = x
      · subst y; simp
      · simp only [Names.bind_other _ hyx]
        rw [h y (by simp [hy, hyx])]

/-- Commute named interpretation with capture-free bound renaming. -/
theorem interpretNamed_rename (e : Expr) (η : Names Γ) (ρ : Ren Γ Δ) :
    interpretNamed e (η.rename ρ) = (interpretNamed e η).map (Packed.rename ρ) := by
  induction e generalizing Γ Δ with
  | var => rfl
  | const => rfl
  | app f a ihf iha =>
      simp only [interpretNamed, ihf, iha]
      cases interpretNamed f η <;> cases interpretNamed a η <;>
        simp [Packed.rename_app]
  | lam x b ih =>
      rw [interpretNamed, Names.bind_rename, ih, interpretNamed, Option.map_map,
        Option.map_map]
      rfl

/-- Commute named interpretation with capture-free bound substitution. -/
theorem interpretNamed_subst (e : Expr) (η : Names Γ) (σ : Sub Γ Δ) :
    interpretNamed e (η.subst σ) = (interpretNamed e η).map (Packed.subst σ) := by
  induction e generalizing Γ Δ with
  | var => rfl
  | const => rfl
  | app f a ihf iha =>
      simp only [interpretNamed, ihf, iha]
      cases interpretNamed f η <;> cases interpretNamed a η <;>
        simp [Packed.subst_app]
  | lam x b ih =>
      rw [interpretNamed, Names.bind_subst, ih, interpretNamed, Option.map_map,
        Option.map_map]
      rfl

/-- Infer the source sort independently of the chosen free-variable interpretations. -/
theorem interpretNamed_sort (e : Expr) (η : Names Γ) :
    (interpretNamed e η).map Sigma.fst = e.sort := by
  induction e generalizing Γ with
  | var => rfl
  | const => rfl
  | lam x b ih =>
      have hb := ih (η.bind x)
      cases he : interpretNamed b (η.bind x) with
      | none => simp [interpretNamed, he, Expr.sort, ← hb]
      | some w =>
          rcases w with ⟨t, v⟩
          simp [interpretNamed, he, Packed.lam, Expr.sort, ← hb]
  | app f a ihf iha =>
      have hf := ihf η
      have ha := iha η
      cases he : interpretNamed f η with
      | none => simp [interpretNamed, he, Expr.sort, ← hf]
      | some w =>
          rcases w with ⟨s, v⟩
          cases he' : interpretNamed a η with
          | none =>
              cases s <;> simp [interpretNamed, he, he', Expr.sort, ← hf, ← ha]
          | some w =>
              rcases w with ⟨u, a'⟩
              cases s with
              | arrow s t =>
                  by_cases h : u = s <;>
                    simp [interpretNamed, he, he', Packed.app, Expr.sort, ← hf, ← ha, h]
              | _ => simp [interpretNamed, he, he', Packed.app, Expr.sort, ← hf]

/-- Interpret every sorted source expression at its original sort. -/
theorem interpretNamed_sorted {e : Expr} (h : e.hasSort s) (η : Names Γ) :
    ∃ t : Term Γ s, interpretNamed e η = some ⟨s, t⟩ := by
  have hs := (interpretNamed_sort e η).trans h
  cases he : interpretNamed e η with
  | none => simp [he] at hs
  | some w =>
      rcases w with ⟨u, t⟩
      simp [he] at hs
      subst u
      exact ⟨t, rfl⟩

end Lisa.Lambda
