import Lisa.Lambda.Reification

/-! Typed conversion reconstructs shared named conversion. Complete named
inputs are independent of ambient indexed substitution. -/
namespace Lisa.Lambda

theorem hasSort_of_interpretNamed (h : interpretNamed p η = some ⟨s, e⟩) : p.hasSort s := by
  simpa [h] using (interpretNamed_sort p η).symm

theorem alpha_of_interpretNamed_eq (hp : interpretNamed p Names.free = some ⟨s, e⟩)
    (hq : interpretNamed q Names.free = some ⟨s, e⟩) : AlphaEq p q :=
  (alpha_iff_interpretNamed_eq (hasSort_of_interpretNamed hp) (hasSort_of_interpretNamed hq)).mpr (hp.trans hq.symm)

namespace Context

def rename (ρ : Context) (τ : Ren) : Context where
  lookup s n := ρ.lookup s (τ s n)
  used := ρ.used
  lookup_mem s n := ρ.lookup_mem s (τ s n)

theorem extend_shift (ρ : Context) (x : SVar) (s : LSort) (n : Nat) :
    (ρ.extend x).lookup s (Ren.shift x.sort s n) = ρ.lookup s n := by
  by_cases h : s = x.sort <;> simp [extend, Ren.shift, h]
end Context

private theorem reify_under_binder (b : Term t) (ρ : Context) (x : SVar)
    (hx : x ∉ b.freeVars) (hu : x.id ∉ ρ.used x.sort) :
    interpretNamed (b.reify (ρ.extend x)) (Names.free.bind x) = some ⟨t, b.subst (ρ.toSub.lift x.sort)⟩ := by
  apply interpretNamed_reify
  · intro y hy
    simp [Names.bind_other _ (show y ≠ x from fun h => hx (h ▸ hy)), Names.free, Term.rename]
  · intro s n
    by_cases h : s = x.sort
    · subst s; cases n with
      | zero => rw [Context.extend_zero, Sub.lift_zero]; exact Names.bind_self _ _
      | succ n =>
          rw [Context.extend_succ]
          simp [Names.bind_other _ (ρ.ne_lookup_of_unused hu x.sort n), Context.toSub, Sub.lift, Names.free, Term.rename]
    · rw [Context.extend_other h]
      simp [Names.bind_other _ (ρ.ne_lookup_of_unused hu s n), Context.toSub, Sub.lift, h, Names.free, Term.rename]

theorem reify_lam_at (b : Term t) (ρ : Context) (x : SVar)
    (hx : x ∉ b.freeVars) (hu : x.id ∉ ρ.used x.sort) :
    AlphaEq ((Term.lam x.sort b).reify ρ) (.lam x (b.reify (ρ.extend x))) := by
  apply alpha_of_interpretNamed_eq (interpretNamed_reify_free _ _)
  simpa [interpretNamed, Packed.lam, Term.subst] using
    congrArg (Option.map (Packed.lam x.sort)) (reify_under_binder b ρ x hx hu)

theorem reify_rename (e : Term s) (τ : Ren) (ρ : Context) :
    AlphaEq ((e.rename τ).reify ρ) (e.reify (ρ.rename τ)) := by
  apply alpha_of_interpretNamed_eq (interpretNamed_reify_free _ _)
  simpa only [Term.subst_rename, Context.toSub, Context.rename] using interpretNamed_reify_free e (ρ.rename τ)

theorem reify_weaken (e : Term t) (ρ : Context) (x : SVar) :
    AlphaEq ((e.shift x.sort).reify (ρ.extend x)) (e.reify ρ) := by
  apply alpha_of_interpretNamed_eq (interpretNamed_reify_free _ _)
  simpa only [Term.subst_rename, Context.toSub, Context.extend_shift] using interpretNamed_reify_free e ρ

private theorem reify_beta (b : Term t) (a : Term s) (ρ : Context) :
    AlphaBetaEta ((Term.app (.lam s b) a).reify ρ) ((b.instantiate a).reify ρ) := by
  let x := ρ.fresh b.freeVars s
  have hx := ρ.fresh_not_mem b.freeVars s
  have hu := ρ.fresh_not_used b.freeVars s
  apply (AlphaBetaEta.app (.alpha (reify_lam_at b ρ x hx hu)) (.refl _)).trans
  apply (AlphaBetaEta.beta x _ _ (by simp [Expr.hasSort, x, Context.fresh])).trans
  have hs : interpretNamed (Expr.substOne x (a.reify ρ) (b.reify (ρ.extend x))) Names.free =
      some ⟨t, (b.instantiate a).subst ρ.toSub⟩ := by
    rw [interpretNamed_substOne _ _ _ _ _ (interpretNamed_reify_free a ρ), reify_under_binder b ρ x hx hu]
    simpa only [Option.map_some, Packed.subst, x, Context.fresh] using
      congrArg (fun e : Term t => some (⟨t, e⟩ : Packed.Expr)) (Term.instantiate_subst_comp b a ρ.toSub).symm
  exact .alpha (alpha_of_interpretNamed_eq hs (interpretNamed_reify_free _ _))

private theorem reify_eta (f : Term (s >> t)) (ρ : Context) :
    AlphaBetaEta ((Term.lam s (.app (f.shift s) (.bound 0))).reify ρ) (f.reify ρ) := by
  let x := ρ.fresh f.freeVars s
  have hx := ρ.fresh_not_mem f.freeVars s
  have hu := ρ.fresh_not_used f.freeVars s
  apply (AlphaBetaEta.alpha (reify_lam_at _ ρ x (by simpa using hx) hu)).trans
  apply (AlphaBetaEta.lam x (.app (.alpha (reify_weaken f ρ x)) (.refl _))).trans
  change AlphaBetaEta (.lam x (.app (f.reify ρ) (.var ⟨(ρ.extend x).lookup x.sort 0, x.sort⟩))) (f.reify ρ)
  rw [Context.extend_zero]
  exact .eta x _ t (by simp [Expr.hasSort, x, Context.fresh]) (fun h =>
    (f.reify_freeVars ρ x h).elim hx hu)

/-- Interpret every intrinsic conversion using Lisa's named conversion rules. -/

theorem Equiv.reify (h : Equiv e f) (ρ : Context) : AlphaBetaEta (e.reify ρ) (f.reify ρ) := by
  induction h generalizing ρ with
  | refl => exact .refl _
  | symm _ ih => exact (ih ρ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ ρ).trans (ih₂ ρ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | @lam t b c s h ih =>
      let x := ρ.fresh (b.freeVars ∪ c.freeVars) s
      have hx := ρ.fresh_not_mem (b.freeVars ∪ c.freeVars) s
      have hu := ρ.fresh_not_used (b.freeVars ∪ c.freeVars) s
      have hb := reify_lam_at b ρ x (fun h => hx (Finset.mem_union_left _ h)) hu
      have hc := reify_lam_at c ρ x (fun h => hx (Finset.mem_union_right _ h)) hu
      exact (AlphaBetaEta.alpha hb).trans ((AlphaBetaEta.lam x (ih (ρ.extend x))).trans (AlphaBetaEta.alpha hc).symm)
  | beta b a => exact reify_beta b a ρ
  | eta f => exact reify_eta f ρ

/-- A complete named input has no ambient indices, expressed using substitution. -/

theorem subst_of_interpretNamed (h : interpretNamed p Names.free = some ⟨s, e⟩) (σ : Sub) : e.subst σ = e := by
  have hh := interpretNamed_subst p Names.free σ
  have hf : Names.free.subst σ = Names.free := rfl
  rw [hf, h] at hh
  simpa [Packed.subst] using hh.symm

theorem alpha_reify_of_interpretNamed (h : interpretNamed p Names.free = some ⟨s, e⟩) (ρ : Context) :
    AlphaEq p (e.reify ρ) := by
  apply alpha_of_interpretNamed_eq h
  simp [subst_of_interpretNamed h]
end Lisa.Lambda
