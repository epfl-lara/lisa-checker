import Lisa.AlphaBetaEta
import Lisa.Lambda.AlphaBetaEta

/-! Interpret named syntax in sorted environments before comparing substitutions. -/

namespace Lisa.Lambda

abbrev Names  := (x : SVar) → Term x.sort

namespace Names

def free : Names := fun x => .free x.id

def rename (η : Names) (ρ : Ren) : Names := fun x => (η x).rename ρ

def subst (η : Names) (σ : Sub) : Names := fun x => (η x).subst σ

/-- Bind the selected name and weaken every other interpretation. -/

def bind (η : Names) (x : SVar) : Names := fun y =>
  if h : y = x then h.symm ▸ (Term.bound 0 : Term x.sort)
  else (η y).rename (Ren.shift x.sort)

@[simp] theorem bind_self (η : Names) (x : SVar) : η.bind x x = .bound 0 := by
  simp [bind]

@[simp] theorem bind_other (η : Names) (h : y ≠ x) :
    η.bind x y = (η y).rename (Ren.shift x.sort) := by
  simp [bind, h]

theorem bind_rename (η : Names) (ρ : Ren) (x : SVar) :
    (η.rename ρ).bind x = (η.bind x).rename (Ren.lift x.sort ρ) := by
  funext y
  by_cases h : y = x
  · subst y; simp [rename, Term.rename]
  · simp only [bind_other _ h, rename, Term.rename_comp, Ren.lift_shift]

theorem bind_subst (η : Names) (σ : Sub) (x : SVar) :
    (η.subst σ).bind x = (η.bind x).subst (Sub.lift x.sort σ) := by
  funext y
  by_cases h : y = x
  · subst y; simp [subst, Term.subst]
  · simp only [bind_other _ h, subst, Term.rename_subst, Term.subst_rename]
    congr 1
    funext s n
    by_cases hs : s = x.sort <;> simp [Sub.lift, Ren.shift, hs]

end Names



/-- Resolve binders and free names while rejecting precisely ill-sorted applications. -/

def interpretNamed : (e : Expr) → Names → Option (Packed.Expr)
  | .var x, η => some ⟨x.sort, η x⟩
  | .const c, _ => some ⟨c.sort, .const c.id⟩
  | .app f a, η => do
      let f' ← interpretNamed f η
      let a' ← interpretNamed a η
      Packed.app f' a'
  | .lam x b, η => (interpretNamed b (η.bind x)).map (Packed.lam x.sort)

/-- Ignore environment entries outside the expression's free variables. -/

theorem interpretNamed_support (e : Expr) (η θ : Names)
    (h : ∀ x ∈ e.freeVars, η x = θ x) : interpretNamed e η = interpretNamed e θ := by
  induction e generalizing η θ with
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

theorem interpretNamed_rename (e : Expr) (η : Names) (ρ : Ren) :
    interpretNamed e (η.rename ρ) = (interpretNamed e η).map (Packed.rename ρ) := by
  induction e generalizing η ρ with
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

theorem interpretNamed_subst (e : Expr) (η : Names) (σ : Sub) :
    interpretNamed e (η.subst σ) = (interpretNamed e η).map (Packed.subst σ) := by
  induction e generalizing η σ with
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

theorem interpretNamed_sort (e : Expr) (η : Names) :
    (interpretNamed e η).map Sigma.fst = e.sort := by
  induction e generalizing η with
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

theorem interpretNamed_sorted {e : Expr} (h : e.hasSort s) (η : Names) :
    ∃ t : Term s, interpretNamed e η = some ⟨s, t⟩ := by
  have hs := (interpretNamed_sort e η).trans h
  cases he : interpretNamed e η with
  | none => simp [he] at hs
  | some w =>
      rcases w with ⟨u, t⟩
      simp [he] at hs
      subst u
      exact ⟨t, rfl⟩

end Lisa.Lambda
