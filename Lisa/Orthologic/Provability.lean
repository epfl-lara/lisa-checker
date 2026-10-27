import Lisa.Orthologic.Syntax
import Lisa.Orthologic.Congruence

/-! Provability and constructor lemmas for the internal LambdaFOL syntax.

Binder proofs quantify over the common naming assignment used to reconstruct
expressions. The two sides need not choose the same binder name on their own:
`reify_lam_at` changes both to a common fresh name by alpha-equivalence.
-/

namespace Lisa.Orthologic
open Expr Derivation

namespace SimpleExpr

theorem reify_all_at (p : SimpleExpr prop) (ρ : Lambda.Context) (x : SVar)
    (hs : x.sort = ind) (hx : x ∉ p.toTerm.freeVars) (hu : x.id ∉ ρ.used x.sort) :
    AlphaBetaEta ((all p).reify ρ) (forall_ x (p.reify (ρ.extend x))) := by
  have h := Lambda.reify_lam_at p.toTerm ρ x hx hu
  rw [hs] at h
  unfold reify
  rw [toTerm]
  exact .app (.refl _) (.alpha h)

/-- Soundness of the positive quantifier case, including binder reconstruction. -/
noncomputable def all_mono (p q : SimpleExpr prop)
    (body : ∀ ρ, Entails (p.reify ρ) (q.reify ρ)) (ρ : Lambda.Context) :
    Entails ((all p).reify ρ) ((all q).reify ρ) := by
  let x := ρ.fresh (p.toTerm.freeVars ∪ q.toTerm.freeVars) ind
  have hx := ρ.fresh_not_mem (p.toTerm.freeVars ∪ q.toTerm.freeVars) ind
  have hu := ρ.fresh_not_used (p.toTerm.freeVars ∪ q.toTerm.freeVars) ind
  have hp := p.reify_all_at ρ x rfl (fun h => hx (Finset.mem_union_left _ h)) hu
  have hq := q.reify_all_at ρ x rfl (fun h => hx (Finset.mem_union_right _ h)) hu
  have d := Derivation.forall_mono x rfl (p.reify_sort _) (q.reify_sort _) (body (ρ.extend x))
  exact Derivation.convert (isFormula_forall rfl (p.reify_sort _))
    (isFormula_forall rfl (q.reify_sort _)) hp.symm hq.symm d

/-- Negative quantifiers reverse the direction of the body comparison. -/
noncomputable def neg_all_mono (p q : SimpleExpr prop)
    (body : ∀ ρ, Entails (q.reify ρ) (p.reify ρ)) (ρ : Lambda.Context) :
    Entails ((neg (all p)).reify ρ) ((neg (all q)).reify ρ) := by
  simpa only [reify_neg] using
    Derivation.neg_mono ((all q).reify_sort _) ((all p).reify_sort _) (q.all_mono p body ρ)

end SimpleExpr

/-- A comparison justified by the ordinary proof rules, under every naming assignment. -/
def ProvableLE (p q : SimpleExpr prop) : Prop :=
  ∀ ρ, Nonempty (Entails (p.reify ρ) (q.reify ρ))

/-- Equivalence usable inside any expression constructor, at any sort. -/
def ProvableEQ (p q : SimpleExpr s) : Prop :=
  ∀ ρ, ContextEq s (p.reify ρ) (q.reify ρ)

namespace ProvableLE
open SimpleExpr
variable {p q r : SimpleExpr prop}

theorem refl (p : SimpleExpr prop) : ProvableLE p p := fun ρ => ⟨.hypothesis _ (p.reify_sort ρ)⟩

theorem trans (h : ProvableLE p q) (j : ProvableLE q r) : ProvableLE p r := by
  intro ρ
  obtain ⟨d⟩ := h ρ
  obtain ⟨e⟩ := j ρ
  exact ⟨Derivation.trans (p.reify_sort _) (q.reify_sort _) (r.reify_sort _) d e⟩

theorem top (p : SimpleExpr prop) : ProvableLE p .top := by
  intro ρ; simpa using Nonempty.intro (Derivation.le_top (p.reify_sort ρ))

theorem bot (p : SimpleExpr prop) : ProvableLE (.neg .top) p := by
  intro ρ
  simpa using Nonempty.intro (Derivation.trans (isFormula_neg (show isFormula Expr.top from rfl))
    (show isFormula Expr.bot from rfl) (p.reify_sort ρ) false_of_neg_top (bot_le (p.reify_sort ρ)))

theorem neg (h : ProvableLE p q) : ProvableLE (.neg q) (.neg p) := by
  intro ρ; obtain ⟨d⟩ := h ρ
  simpa using Nonempty.intro (neg_mono (p.reify_sort _) (q.reify_sort _) d)

theorem doubleNegIntro (p : SimpleExpr prop) : ProvableLE p (.neg (.neg p)) := by
  intro ρ; simpa using Nonempty.intro (Derivation.doubleNegIntro (p.reify_sort ρ))

theorem doubleNegElim (p : SimpleExpr prop) : ProvableLE (.neg (.neg p)) p := by
  intro ρ; simpa using Nonempty.intro (Derivation.doubleNegElim (p.reify_sort ρ))

theorem conj_right (ps : List (SimpleExpr prop)) (h : ∀ q ∈ ps, ProvableLE p q) :
    ProvableLE p (.conj ps) := by
  intro ρ
  rw [SimpleExpr.reify_conj]
  cases ps with
  | nil => exact ⟨le_top (p.reify_sort ρ)⟩
  | cons q qs =>
      apply le_fold_and (p.reify_sort _) (q.reify_sort _)
      · intro r hr; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr; exact a.reify_sort _
      · exact h q (by simp) ρ
      · intro r hr; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr; exact h a (by simp [ha]) ρ

theorem conj_member (ps : List (SimpleExpr prop)) (hp : p ∈ ps) : ProvableLE (.conj ps) p := by
  intro ρ
  rw [SimpleExpr.reify_conj]
  cases ps with
  | nil => simp at hp
  | cons q qs =>
      have hs : ∀ r ∈ qs.map (fun p => p.reify ρ), isFormula r := by
        intro r hr; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr; exact a.reify_sort _
      have h := fold_and_le (q.reify_sort ρ) hs
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h.1
      · exact h.2 _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem neg_conj_left (ps : List (SimpleExpr prop)) (h : ∀ p ∈ ps, ProvableLE (.neg p) q) :
    ProvableLE (.neg (.conj ps)) q := by
  have d : ProvableLE (.neg q) (.conj ps) :=
    conj_right ps (fun p hp => (h p hp).neg.trans (doubleNegElim p))
  exact d.neg.trans (doubleNegElim q)

theorem all (h : ProvableLE p q) : ProvableLE (.all p) (.all q) := by
  classical
  intro ρ
  exact ⟨SimpleExpr.all_mono p q (fun ρ => Classical.choice (h ρ)) ρ⟩

end ProvableLE

namespace ProvableEQ
open SimpleExpr
variable {s t : LSort} {p q r : SimpleExpr s}

theorem refl (p : SimpleExpr s) : ProvableEQ p p := fun ρ => ContextEq.refl (p.reify_sort ρ)
theorem symm (h : ProvableEQ p q) : ProvableEQ q p := fun ρ => (h ρ).symm
theorem trans (h : ProvableEQ p q) (j : ProvableEQ q r) : ProvableEQ p r :=
  fun ρ => ContextEq.trans (p.reify_sort _) (q.reify_sort _) (r.reify_sort _) (h ρ) (j ρ)

theorem of_toTerm (h : p.toTerm = q.toTerm) : ProvableEQ p q := by
  intro ρ
  have hr : p.reify ρ = q.reify ρ := congrArg (fun t => t.reify ρ) h
  rw [hr]; exact ContextEq.refl (q.reify_sort ρ)

theorem of_le {p q : SimpleExpr prop} (h : ProvableLE p q) (j : ProvableLE q p) : ProvableEQ p q :=
  fun ρ => ContextEq.of_formula (p.reify_sort _) (q.reify_sort _) (h ρ) (j ρ)

theorem le {p q : SimpleExpr prop} (h : ProvableEQ p q) : ProvableLE p q :=
  fun ρ => (ContextEq.formula (p.reify_sort _) (q.reify_sort _) (h ρ)).1

theorem app {f g : SimpleExpr (s >> t)} {a b : SimpleExpr s}
    (h : ProvableEQ f g) (j : ProvableEQ a b) : ProvableEQ (.app f a) (.app g b) := by
  intro ρ; simp only [reify_app]
  exact ContextEq.app (f.reify_sort _) (g.reify_sort _) (a.reify_sort _) (b.reify_sort _) (h ρ) (j ρ)

theorem lam (s : LSort) {p q : SimpleExpr t} (h : ProvableEQ p q) :
    ProvableEQ (.lam s p) (.lam s q) := by
  intro ρ
  let x := ρ.fresh (p.toTerm.freeVars ∪ q.toTerm.freeVars) s
  have hx := ρ.fresh_not_mem (p.toTerm.freeVars ∪ q.toTerm.freeVars) s
  have hu := ρ.fresh_not_used (p.toTerm.freeVars ∪ q.toTerm.freeVars) s
  have hp : AlphaBetaEta ((SimpleExpr.lam s p).reify ρ) (.lam x (p.reify (ρ.extend x))) := by
    unfold reify; rw [toTerm]
    exact .alpha (Lambda.reify_lam_at p.toTerm ρ x (fun hm => hx (Finset.mem_union_left _ hm)) hu)
  have hq : AlphaBetaEta ((SimpleExpr.lam s q).reify ρ) (.lam x (q.reify (ρ.extend x))) := by
    unfold reify; rw [toTerm]
    exact .alpha (Lambda.reify_lam_at q.toTerm ρ x (fun hm => hx (Finset.mem_union_right _ hm)) hu)
  have hp' := hp.preserves_sort.symm.trans ((SimpleExpr.lam s p).reify_sort ρ)
  have hq' := hq.preserves_sort.symm.trans ((SimpleExpr.lam s q).reify_sort ρ)
  exact ContextEq.trans ((SimpleExpr.lam s p).reify_sort _) hp' ((SimpleExpr.lam s q).reify_sort _)
    (ContextEq.of_conversion ((SimpleExpr.lam s p).reify_sort _) hp)
    (ContextEq.trans hp' hq' ((SimpleExpr.lam s q).reify_sort _)
      (ContextEq.lam x (p.reify_sort _) (q.reify_sort _) (h (ρ.extend x)))
      (ContextEq.of_conversion hq' hq.symm))

theorem neg {p q : SimpleExpr prop} (h : ProvableEQ p q) : ProvableEQ (.neg p) (.neg q) :=
  of_le h.symm.le.neg h.le.neg

theorem all {p q : SimpleExpr prop} (h : ProvableEQ p q) : ProvableEQ (.all p) (.all q) :=
  of_le h.le.all h.symm.le.all

theorem equal {a b c d : SimpleExpr ind} (h : ProvableEQ a c) (j : ProvableEQ b d) :
    ProvableEQ (.equal a b) (.equal c d) := by
  intro ρ; simp only [reify_equal]
  exact ContextEq.app (ContextEq.app_sort rfl (a.reify_sort _))
    (ContextEq.app_sort rfl (c.reify_sort _)) (b.reify_sort _) (d.reify_sort _)
    (ContextEq.app_right (show (Expr.const (SConst.named "eq" (ind >> ind >> prop))).hasSort (ind >> ind >> prop) from rfl)
      (a.reify_sort _) (c.reify_sort _) (h ρ)) (j ρ)

theorem equal_symm (a b : SimpleExpr ind) : ProvableEQ (.equal a b) (.equal b a) := by
  apply of_le <;> intro ρ <;> simp only [reify_equal]
  · exact ⟨Derivation.eq_symm (a.reify_sort _) (b.reify_sort _)⟩
  · exact ⟨Derivation.eq_symm (b.reify_sort _) (a.reify_sort _)⟩

end ProvableEQ
end Lisa.Orthologic
