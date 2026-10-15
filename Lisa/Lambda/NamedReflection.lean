import Lisa.Lambda.Reification

namespace Lisa.Lambda

theorem hasSort_of_interpretNamed {p : Expr} {e : Term Γ s}
    (h : interpretNamed p η = some ⟨s, e⟩) : p.hasSort s := by
  simpa [h] using (interpretNamed_sort p η).symm

/-- Recover alpha-equivalence from an identical successful typed interpretation. -/
theorem alpha_of_interpretNamed_eq {p q : Expr} {e : Term [] s}
    (hp : interpretNamed p Names.free = some ⟨s, e⟩)
    (hq : interpretNamed q Names.free = some ⟨s, e⟩) : AlphaEq p q :=
  (alpha_iff_interpretNamed_eq (hasSort_of_interpretNamed hp)
    (hasSort_of_interpretNamed hq)).mpr (hp.trans hq.symm)

private theorem reify_under_binder (b : Term (s :: Γ) t) (ρ : Context Γ) (id : Identifier)
    (hx : (⟨id, s⟩ : SVar) ∉ b.freeVars ∪ ρ.vars) :
    interpretNamed (b.reify (ρ.extend id)) (Names.free.bind ⟨id, s⟩) =
      some ⟨t, b.subst (Sub.lift ρ.toSub)⟩ := by
  apply interpretNamed_reify
  · intro y hy
    have h : y ≠ ⟨id, s⟩ := fun h => hx (h ▸ Finset.mem_union_left _ hy)
    simp [Names.bind_other _ h, Names.free, Term.rename]
  · intro u v
    cases v with
    | here => exact Names.bind_self _ _
    | there v =>
        have h : (⟨ρ v, u⟩ : SVar) ≠ ⟨id, s⟩ :=
          fun h => hx (h ▸ Finset.mem_union_right _ (ρ.mem_vars v))
        simp [Context.extend, Names.bind_other _ h, Context.toSub, Sub.lift,
          Names.free, Term.rename]

/-- Choose any fresh binder when reconstructing an abstraction. -/
theorem reify_lam_at (b : Term (s :: Γ) t) (ρ : Context Γ) (id : Identifier)
    (hx : (⟨id, s⟩ : SVar) ∉ b.freeVars ∪ ρ.vars) :
    AlphaEq ((Term.lam b).reify ρ) (.lam ⟨id, s⟩ (b.reify (ρ.extend id))) := by
  apply alpha_of_interpretNamed_eq (interpretNamed_reify_free _ _)
  simpa [interpretNamed, Packed.lam, Term.subst] using
    congrArg (Option.map (Packed.lam s)) (reify_under_binder b ρ id hx)

/-- Reconstruct bound renaming as an alpha-equivalent change of the naming context. -/
theorem reify_rename (e : Term Γ s) (τ : Ren Γ Δ) (ρ : Context Δ) :
    AlphaEq ((e.rename τ).reify ρ) (e.reify (fun v => ρ (τ v))) := by
  apply alpha_of_interpretNamed_eq (interpretNamed_reify_free _ _)
  simpa only [Term.subst_rename, Context.toSub] using
    interpretNamed_reify_free e (fun v => ρ (τ v))

theorem reify_weaken (e : Term Γ t) (ρ : Context Γ) (id : Identifier) (s : LSort) :
    AlphaEq ((e.rename (Var.there : Ren Γ (s :: Γ))).reify (ρ.extend id)) (e.reify ρ) := by
  simpa only [Context.extend] using reify_rename e Var.there (ρ.extend id)

private theorem reify_beta (b : Term (s :: Γ) t) (a : Term Γ s) (ρ : Context Γ) :
    Conversion ((Term.app (.lam b) a).reify ρ) ((b.instantiate a).reify ρ) := by
  let x := ρ.fresh b.freeVars s
  have hx := ρ.fresh_not_mem b.freeVars s
  have hb : AlphaEq ((Term.lam b).reify ρ) (.lam x (b.reify (ρ.extend x.id))) :=
    reify_lam_at b ρ x.id hx
  apply (Conversion.app (.alpha hb) (.refl _)).trans
  apply (Conversion.beta x _ _ (by simp [Expr.hasSort, x, Context.fresh])).trans
  have hi := reify_under_binder b ρ x.id hx
  change interpretNamed (b.reify (ρ.extend x.id)) (Names.free.bind x) = _ at hi
  have hs : interpretNamed (Expr.substOne x (a.reify ρ) (b.reify (ρ.extend x.id)))
      Names.free = some ⟨t, (b.instantiate a).subst ρ.toSub⟩ := by
    rw [interpretNamed_substOne _ _ _ _ _ (interpretNamed_reify_free a ρ), hi]
    simpa only [Option.map_some, Packed.subst, Term.instantiate] using
      congrArg (fun e : Term [] t => some (⟨t, e⟩ : Packed.Expr []))
        (Term.instantiate_subst_comp b a ρ.toSub).symm
  exact .alpha (alpha_of_interpretNamed_eq hs (interpretNamed_reify_free _ _))

private theorem reify_eta (f : Term Γ (s >> t)) (ρ : Context Γ) :
    Conversion
      ((Term.lam (.app (f.rename Var.there) (.bound .here))).reify ρ) (f.reify ρ) := by
  let x := ρ.fresh f.freeVars s
  have hx := ρ.fresh_not_mem f.freeVars s
  apply (Conversion.alpha (reify_lam_at _ ρ x.id (by simpa using hx))).trans
  have hr := reify_weaken f ρ x.id s
  apply (Conversion.lam x (.app (.alpha hr) (.refl _))).trans
  exact .eta x _ t (by simp [Expr.hasSort, x, Context.fresh])
    (fun h => hx (f.reify_freeVars ρ h))

/-- Reconstruct intrinsic conversion using only the original named conversion rules. -/
theorem Equiv.reify {e f : Term Γ s} (h : Equiv e f) (ρ : Context Γ) :
    Conversion (e.reify ρ) (f.reify ρ) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact (ih ρ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ ρ).trans (ih₂ ρ)
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | @lam s Γ t b c h ih =>
      let x := ρ.fresh (b.freeVars ∪ c.freeVars) s
      have hx := ρ.fresh_not_mem (b.freeVars ∪ c.freeVars) s
      have hb : x ∉ b.freeVars ∪ ρ.vars := by
        intro hm
        apply hx
        simpa only [Finset.mem_union] using
          (Finset.mem_union.mp hm).imp (fun h => Or.inl h) id
      have hc : x ∉ c.freeVars ∪ ρ.vars := by
        intro hm
        apply hx
        simpa only [Finset.mem_union] using
          (Finset.mem_union.mp hm).imp (fun h => Or.inr h) id
      exact (Conversion.alpha (reify_lam_at b ρ x.id hb)).trans
        ((Conversion.lam x (ih (ρ.extend x.id))).trans
          (Conversion.alpha (reify_lam_at c ρ x.id hc)).symm)
  | beta b a => exact reify_beta b a ρ
  | eta f => exact reify_eta f ρ

@[simp] theorem Term.subst_empty (e : Term [] s) : e.subst Context.empty.toSub = e := by
  have h : (Context.empty.toSub : Sub [] []) = @Sub.id [] := by
    funext t v
    nomatch v
  rw [h, Term.subst_id]

@[simp] theorem elaborate_reify (e : Term [] s) :
    elaborate [] ((e.reify Context.empty).toNameless []) = some ⟨s, e⟩ := by
  rw [← interpretNamed_free, interpretNamed_reify_free, Term.subst_empty]

/-- Reconstruct the same named alpha-class after typed elaboration. -/
theorem alpha_reify_of_elaborate {p : Expr} {e : Term [] s}
    (hp : elaborate [] (p.toNameless []) = some ⟨s, e⟩) :
    AlphaEq p (e.reify Context.empty) := by
  apply alpha_of_interpretNamed_eq
  · rwa [interpretNamed_free]
  · simp

/-- Reflect every successful intrinsic comparison into the original named relation. -/
theorem conversion_of_compareNameless {p q : Expr}
    (h : compareNameless [] (p.toNameless []) (q.toNameless []) = some true) :
    Conversion p q := by
  obtain ⟨s, e, f, hp, hq, he⟩ := (compareNameless_true _ _ _).mp h
  exact (Conversion.alpha (alpha_reify_of_elaborate hp)).trans
    ((he.reify Context.empty).trans (Conversion.alpha (alpha_reify_of_elaborate hq)).symm)

/-- Characterize total intrinsic comparison on the original well-sorted named syntax. -/
theorem compareNameless_iff_conversion {p q : Expr} (hp : p.hasSort s) :
    compareNameless [] (p.toNameless []) (q.toNameless []) = some true ↔ Conversion p q :=
  ⟨conversion_of_compareNameless, fun h => compareNameless_of_conversion h hp⟩

end Lisa.Lambda
