import Lisa.Lambda.Evaluation

namespace Lisa.Lambda

/-- Relate syntax to semantic values by testing functions on related arguments. -/
def Related : (s : LSort) → Term Γ s → Val Γ s → Prop
  | .ind, e, v => Equiv e v
  | .prop, e, v => Equiv e v
  | .arrow s t, e, v => ∀ {Δ} (ρ : Ren Γ Δ) (a : Term Δ s) (w : Val Δ s),
      Related s a w → Related t (.app (e.rename ρ) a) (v.run ρ w)

namespace Related

theorem congr {e f : Term Γ s} {v : Val Γ s} (h : Related s e v)
    (hef : Equiv e f) : Related s f v := by
  induction s generalizing Γ with
  | ind => exact hef.symm.trans h
  | prop => exact hef.symm.trans h
  | arrow s t _ iht =>
      intro Δ ρ a w ha
      exact iht (h ρ a w ha) (.app (hef.rename ρ) (.refl a))

theorem rename {e : Term Γ s} {v : Val Γ s} (h : Related s e v) (ρ : Ren Γ Δ) :
    Related s (e.rename ρ) ((model s).values.map ρ v) := by
  induction s generalizing Γ Δ with
  | ind => exact Equiv.rename h ρ
  | prop => exact Equiv.rename h ρ
  | arrow s t =>
      intro Θ τ a w ha
      simpa only [Term.rename_comp] using h (Ren.comp ρ τ) a w ha

end Related

/-- Prove readback and reflection together by induction on the sort. -/
theorem readback_correct (s : LSort) :
    (∀ {Γ} (e : Term Γ s) (v : Val Γ s), Related s e v →
      Equiv e ((model s).quote v)) ∧
    (∀ {Γ} (e : Term Γ s), Related s e ((model s).reflect e)) := by
  induction s with
  | ind => exact ⟨fun _ _ h => h, fun _ => .refl _⟩
  | prop => exact ⟨fun _ _ h => h, fun _ => .refl _⟩
  | arrow s t ihs iht =>
      constructor
      · intro Γ e v h
        have hb := iht.1 _ _ (h Var.there (.bound .here) _ (ihs.2 _))
        exact (Equiv.eta e).symm.trans (.lam hb)
      · intro Γ e Δ ρ a w ha
        have h := iht.2 (.app (e.rename ρ) ((model s).quote w))
        exact h.congr (.app (.refl _) (ihs.1 a w ha).symm)

namespace Term

theorem subst_lift_rename (b : Term (s :: Γ) t) (σ : Sub Γ Δ) (ρ : Ren Δ Θ) :
    (b.subst (Sub.lift σ)).rename (Ren.lift ρ) =
      b.subst (Sub.lift (fun v => (σ v).rename ρ)) := by
  rw [rename_subst]
  congr 1
  funext u v
  cases v with
  | here => rfl
  | there v =>
      simp only [Sub.lift, rename_comp]
      rfl

end Term

/-- Relate simultaneous syntactic substitution to semantic evaluation. -/
theorem fundamental (e : Term Γ s) (σ : Sub Γ Δ) (η : Env Γ Δ)
    (h : ∀ {t} (v : Var Γ t), Related t (σ v) (η v)) :
    Related s (e.subst σ) (eval e η) := by
  induction e generalizing Δ with
  | bound v => exact h v
  | free x => exact (readback_correct _).2 (.free x)
  | const c => exact (readback_correct _).2 (.const c)
  | app f a ihf iha =>
      simpa only [Term.rename_id] using ihf σ η h Ren.id _ _ (iha σ η h)
  | lam b ih =>
      intro Θ ρ a w ha
      let σ' : Sub _ Θ := fun v => (σ v).rename ρ
      have h' : ∀ {u} (v : Var _ u),
          Related u (Sub.extend σ' a v) (Env.extend (Env.rename η ρ) w v) := by
        intro u v
        cases v with
        | here => exact ha
        | there v => exact (h v).rename ρ
      have hb := ih (Sub.extend σ' a) (Env.extend (Env.rename η ρ) w) h'
      have hβ := Equiv.beta ((b.subst (Sub.lift σ)).rename (Ren.lift ρ)) a
      rw [Term.subst_lift_rename, Term.instantiate_subst] at hβ
      simp only [Term.subst, Term.rename, Term.subst_lift_rename]
      exact hb.congr hβ.symm

/-- Return a beta-eta equivalent term by a total, structurally recursive procedure. -/
theorem normalize_sound (e : Term Γ s) : Equiv e (normalize e) := by
  have h := fundamental e Sub.id (fun v => (model _).reflect (.bound v))
    (fun v => (readback_correct _).2 (.bound v))
  rw [Term.subst_id] at h
  exact (readback_correct s).1 _ _ h

/-- Characterize beta-eta equivalence by syntactic equality of total readbacks. -/
theorem equiv_iff_normalize_eq (e f : Term Γ s) :
    Equiv e f ↔ normalize e = normalize f := by
  constructor
  · exact normalize_eq_of_equiv
  · intro h
    exact (normalize_sound e).trans (h ▸ (normalize_sound f).symm)

@[simp] theorem normalize_idempotent (e : Term Γ s) :
    normalize (normalize e) = normalize e :=
  (normalize_eq_of_equiv (normalize_sound e)).symm

end Lisa.Lambda
