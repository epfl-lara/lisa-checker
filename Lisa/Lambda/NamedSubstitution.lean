import Lisa.Lambda.NamedEnvironment

namespace Lisa
namespace Subst

theorem lookup_without (σ : Subst) (x y : SVar) :
    (σ.without x).find? y = if y = x then none else σ.find? y := by
  induction σ with
  | nil => simp [without, Lean.AssocList.find?]
  | cons z e rest ih =>
      by_cases hzx : z = x <;> by_cases hzy : z = y <;> by_cases hyx : y = x <;>
        simp_all [without, Lean.AssocList.find?, Bool.beq_eq_decide_eq]

private theorem lookup_replace_other (σ : Subst) (x y : SVar) (e : Expr) (h : y ≠ x) :
    (σ.replace x e).find? y = σ.find? y := by
  induction σ with
  | nil => rfl
  | cons z v rest ih =>
      by_cases hzx : z = x <;> by_cases hzy : z = y <;>
        simp_all [Lean.AssocList.replace, Lean.AssocList.find?, Bool.beq_eq_decide_eq]

private theorem lookup_replace_self (σ : Subst) (x : SVar) (e : Expr)
    (h : σ.contains x = true) : (σ.replace x e).find? x = some e := by
  induction σ with
  | nil => simp [Lean.AssocList.contains] at h
  | cons z v rest ih =>
      by_cases hzx : z = x
      · subst z; simp [Lean.AssocList.replace, Lean.AssocList.find?]
      · simp [Lean.AssocList.contains, hzx] at h
        simpa [Lean.AssocList.replace, Lean.AssocList.find?, Bool.beq_eq_decide_eq, hzx] using ih h

theorem lookup_insert (σ : Subst) (x y : SVar) (e : Expr) :
    (σ.insert x e).find? y = if y = x then some e else σ.find? y := by
  unfold Lean.AssocList.insert
  by_cases hc : σ.contains x = true
  · simp only [hc, ↓reduceIte]
    by_cases hyx : y = x
    · subst y; simpa using lookup_replace_self σ x e hc
    · simpa [hyx] using lookup_replace_other σ x y e hyx
  · by_cases hyx : y = x
    · subst y; simp [hc, Lean.AssocList.insertNew, Lean.AssocList.find?]
    · simp [hc, Lean.AssocList.insertNew, Lean.AssocList.find?, Bool.beq_eq_decide_eq,
        hyx, Ne.symm hyx]

theorem lookup_freeVars {σ : Subst} {x : SVar} {e : Expr} (h : σ.find? x = some e) :
    e.freeVars ⊆ σ.rangeFreeVars := by
  induction σ with
  | nil => simp [Lean.AssocList.find?] at h
  | cons y v rest ih =>
      by_cases hyx : y = x
      · simp [Lean.AssocList.find?, hyx] at h
        subst v
        exact Finset.subset_union_left
      · simp [Lean.AssocList.find?, Bool.beq_eq_decide_eq, hyx] at h
        exact (ih h).trans Finset.subset_union_right

end Subst

namespace Lambda

/-- Specify how a named substitution acts on the relevant environment entries. -/
def Represents (σ : Subst) (η θ : Names Γ) (xs : Finset SVar) : Prop :=
  ∀ x ∈ xs, match σ.find? x with
    | none => η x = θ x
    | some e => interpretNamed e η = some ⟨x.sort, θ x⟩

/-- Weaken an expression beneath a binder that does not occur freely in it. -/
theorem interpretNamed_bind_fresh (e : Expr) (η : Names Γ) (x : SVar)
    (h : x ∉ e.freeVars) :
    interpretNamed e (η.bind x) = (interpretNamed e η).map (Packed.rename Var.there) := by
  rw [← interpretNamed_rename]
  apply interpretNamed_support
  intro y hy
  exact Names.bind_other η (fun hyx => h (hyx ▸ hy))

/-- Preserve capture-avoiding named substitution exactly, including binder renaming. -/
theorem interpretNamed_namedSubst (e : Expr) (σ : Subst) (η θ : Names Γ)
    (h : Represents σ η θ e.freeVars) :
    interpretNamed (σ.subst e) η = interpretNamed e θ := by
  induction e generalizing Γ σ with
  | var x =>
      have hx := h x (by simp)
      cases he : σ.find? x <;> simpa [Subst.subst, interpretNamed, he] using hx
  | const => rfl
  | app f a ihf iha =>
      simp only [Subst.subst, interpretNamed]
      rw [ihf σ η θ (fun x hx => h x (by simp [hx])),
        iha σ η θ (fun x hx => h x (by simp [hx]))]
  | lam x b ih =>
      simp only [Subst.subst]
      split
      · rename_i hx
        let taken := σ.rangeFreeVars ∪ b.freeVars ∪ σ.domain
        let x' : SVar := { x with id := freshId (taken.image (·.id)) x.id }
        have hfresh : x' ∉ taken := by
          intro hmem
          exact freshId_not_mem (taken.image SVar.id) x.id
            (Finset.mem_image.mpr ⟨x', hmem, rfl⟩)
        have hbody : x' ∉ b.freeVars := fun hmem => hfresh (by simp [taken, hmem])
        have hrange : x' ∉ σ.rangeFreeVars := fun hmem => hfresh (by simp [taken, hmem])
        change (interpretNamed (Subst.subst ((σ.without x).insert x (.var x')) b)
          (η.bind x')).map (Packed.lam x.sort) =
          (interpretNamed b (θ.bind x)).map (Packed.lam x.sort)
        congr 1
        apply ih
        intro y hy
        simp only [Subst.lookup_insert, Subst.lookup_without]
        by_cases hyx : y = x
        · subst y
          simp [interpretNamed, Names.bind_self, x']
        · simp only [hyx, ↓reduceIte]
          have hrel := h y (by simp [hy, hyx])
          have hyx' : y ≠ x' := fun he => hbody (he ▸ hy)
          cases he : σ.find? y with
          | none =>
              simp only [he] at hrel ⊢
              simp only [Names.bind_other _ hyx, Names.bind_other _ hyx', hrel]
          | some v =>
              simp only [he] at hrel ⊢
              rw [interpretNamed_bind_fresh v η x'
                (fun hv => hrange (Subst.lookup_freeVars he hv)), hrel]
              simp [Packed.rename, Names.bind_other _ hyx]
      · rename_i hx
        simp only [interpretNamed]
        congr 1
        apply ih
        intro y hy
        simp only [Subst.lookup_without]
        by_cases hyx : y = x
        · subst y; simp
        · simp only [hyx, ↓reduceIte]
          have hrel := h y (by simp [hy, hyx])
          cases he : σ.find? y with
          | none =>
              simp only [he] at hrel ⊢
              simp only [Names.bind_other _ hyx, hrel]
          | some v =>
              simp only [he] at hrel ⊢
              rw [interpretNamed_bind_fresh v η x
                (fun hv => hx (Subst.lookup_freeVars he hv)), hrel]
              simp [Packed.rename, Names.bind_other _ hyx]

/-- Interpret named beta substitution as instantiation of the innermost typed binder. -/
theorem interpretNamed_substOne (x : SVar) (body arg : Expr) (η : Names Γ)
    (a : Term Γ x.sort) (ha : interpretNamed arg η = some ⟨x.sort, a⟩) :
    interpretNamed (Expr.substOne x arg body) η =
      (interpretNamed body (η.bind x)).map (Packed.subst (Term.single a)) := by
  rw [← interpretNamed_subst]
  apply interpretNamed_namedSubst
  intro y _
  simp only [Subst.lookup_insert, Lean.AssocList.find?]
  by_cases h : y = x
  · subst y
    simpa [Names.subst, Term.subst, Term.single] using ha
  · simp only [h, ↓reduceIte, Names.subst, Names.bind_other _ h]
    exact ((η y).shift_instantiate a).symm

end Lambda
end Lisa
