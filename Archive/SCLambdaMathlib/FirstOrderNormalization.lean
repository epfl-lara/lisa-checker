import Lisa.SCLambdaToPure.FirstOrderShape

/-!
# Normalization fixes first-order syntax

In particular, substituting first-order individual terms in first-order syntax
does not create lambda redexes. The evaluator calculation below is also valid
for open bound indices; it does not assume that the term is a complete formula.
-/

namespace Lisa.SCLambdaToPure.FirstOrderShape

open Lambda

theorem Individual.rename {e : Term s} (h : Individual e) (ρ : Ren) :
    Individual (e.rename ρ) := by
  induction h with
  | bound => exact .bound _
  | free => exact .free _
  | symbol => exact .symbol _ _
  | app _ _ ihf iha => exact .app ihf iha

theorem Individual.subst {e : Term s} (h : Individual e) (σ : Sub)
    (hσ : ∀ n, Individual (σ ind n)) : Individual (e.subst σ) := by
  induction h with
  | bound n => exact hσ n
  | free => exact .free _
  | symbol => exact .symbol _ _
  | app _ _ ihf iha => exact .app ihf iha

theorem Formula.subst {e : Term s} (h : Formula e) (σ : Sub)
    (hσ : ∀ n, Individual (σ ind n)) : Formula (e.subst σ) := by
  induction h generalizing σ with
  | free => exact .free _
  | symbol => exact .symbol _ _
  | top => exact .top
  | bot => exact .bot
  | app _ ha ih => exact .app (ih σ hσ) (ha.subst σ hσ)
  | neg _ ih => exact .neg (ih σ hσ)
  | and _ _ ihp ihq => exact .and (ihp σ hσ) (ihq σ hσ)
  | or _ _ ihp ihq => exact .or (ihp σ hσ) (ihq σ hσ)
  | imp _ _ ihp ihq => exact .imp (ihp σ hσ) (ihq σ hσ)
  | iff _ _ ihp ihq => exact .iff (ihp σ hσ) (ihq σ hσ)
  | eq ht hu => exact .eq (ht.subst σ hσ) (hu.subst σ hσ)
  | all _ ih =>
      apply Formula.all
      apply ih
      intro n; cases n with
      | zero => exact .bound _
      | succ n => exact (hσ n).rename _
  | ex _ ih =>
      apply Formula.ex
      apply ih
      intro n; cases n with
      | zero => exact .bound _
      | succ n => exact (hσ n).rename _

theorem Individual.subst_congr {e : Term s} (h : Individual e) (σ τ : Sub)
    (he : ∀ n, σ ind n = τ ind n) : e.subst σ = e.subst τ := by
  induction h with
  | bound n => exact he n
  | free => rfl
  | symbol => rfl
  | app _ _ ihf iha => exact congrArg₂ Term.app ihf iha

theorem Formula.subst_congr {e : Term s} (h : Formula e) (σ τ : Sub)
    (he : ∀ n, σ ind n = τ ind n) : e.subst σ = e.subst τ := by
  induction h generalizing σ τ with
  | free => rfl
  | symbol => rfl
  | top => rfl
  | bot => rfl
  | app _ ha ih => exact congrArg₂ Term.app (ih σ τ he) (ha.subst_congr σ τ he)
  | neg _ ih => exact congrArg (Term.app _) (ih σ τ he)
  | and _ _ ihp ihq | or _ _ ihp ihq | imp _ _ ihp ihq | iff _ _ ihp ihq =>
      exact congrArg₂ (fun p q => Term.app (.app _ p) q) (ihp σ τ he) (ihq σ τ he)
  | eq ht hu =>
      exact congrArg₂ (fun t u => Term.app (.app _ t) u)
        (ht.subst_congr σ τ he) (hu.subst_congr σ τ he)
  | all _ ih | ex _ ih =>
      apply congrArg (fun p => Term.app _ (.lam ind p))
      apply ih
      intro n; cases n <;> simp [he]

private def atDepth (η : Env) (d : Depth) : Sub
  | .ind, n => η ind n d
  | .prop, n => .bound n
  | .arrow _ _, n => .bound n

private theorem individual_eval {e : Term s} (h : Individual e) (η : Env) :
    eval e η = reflect s (fun d => e.subst (atDepth η d)) := by
  induction h with
  | bound => rfl
  | free => rfl
  | symbol => rfl
  | app _ _ ihf iha =>
      simp only [eval, ihf, iha]
      rfl

private theorem predicate_eval {e : Term s} (h : Formula e) (hs : s ≠ prop) (η : Env) :
    eval e η = reflect s (fun d => e.subst (atDepth η d)) := by
  induction h with
  | free => contradiction
  | symbol => rfl
  | app _ ha ih =>
      rw [eval, ih (by simp), individual_eval ha]
      rfl
  | top => contradiction
  | bot => contradiction
  | neg => contradiction
  | and => contradiction
  | or => contradiction
  | imp => contradiction
  | iff => contradiction
  | eq => contradiction
  | all => contradiction
  | ex => contradiction

private def Assigned (d : Depth) (η : Env) (σ : Sub) : Prop :=
  ∀ n k, d.Extends k → η ind n k = (σ ind n).rename (d.weaken k)

private theorem shift_weaken {d k : Depth} (h : (d.inc b).Extends k) :
    Ren.comp (Ren.shift b) ((d.inc b).weaken k) = d.weaken k := by
  funext s n
  have hs := h s
  by_cases he : s = b
  · subst s
    simp [Ren.comp, Ren.shift, Depth.weaken] at hs ⊢
    omega
  · simp [Ren.comp, Ren.shift, Depth.weaken, he]

private theorem Assigned.extend (h : Assigned d η σ) :
    Assigned (d.inc ind) (η.extend (b := ind) (fresh ind (d ind))) (σ.lift ind) := by
  intro n k hk
  cases n with
  | zero => simp [Env.extend, Sub.lift, fresh, Term.rename, Depth.weaken]
  | succ n =>
      simp only [Env.extend_succ, Sub.lift_succ, Term.rename_comp, shift_weaken hk]
      exact h n k ((Depth.extends_inc d ind).trans hk)

private theorem assigned_here (h : Assigned d η σ) : ∀ n, atDepth η d ind n = σ ind n := by
  intro n
  simpa [atDepth] using h n d (Depth.extends_refl d)

/-- Evaluate a first-order formula by substituting its individual indices.
The environment condition records how their syntax shifts under a quantifier. -/
private theorem formula_eval {e : Term s} (h : Formula e) (hs : s = prop) (η : Env) (σ : Sub)
    (hη : Assigned d η σ) : eval (hs ▸ e : Term prop) η d = (hs ▸ e : Term prop).subst σ := by
  induction h generalizing d η σ with
  | free => rfl
  | symbol n c =>
      cases n with
      | zero => rfl
      | succ n => cases hs
  | @app s f a hf ha ih =>
      cases hs
      simp only [eval, predicate_eval hf (by simp), individual_eval ha]
      change Term.app (f.subst (atDepth η d)) (a.subst (atDepth η d)) = _
      exact congrArg₂ Term.app
        (hf.subst_congr _ _ (assigned_here hη)) (ha.subst_congr _ _ (assigned_here hη))
  | top => rfl
  | bot => rfl
  | neg _ ih =>
      change Term.app _ (eval (s := prop) _ η d) = _
      rw [ih rfl η σ hη]
      rfl
  | and _ _ ihp ihq | or _ _ ihp ihq | imp _ _ ihp ihq | iff _ _ ihp ihq =>
      change Term.app (Term.app _ (eval (s := prop) _ η d)) (eval (s := prop) _ η d) = _
      rw [ihp rfl η σ hη, ihq rfl η σ hη]
      rfl
  | eq ht hu =>
      simp only [eval, individual_eval ht, individual_eval hu]
      exact congrArg₂ (fun t u => Term.app (.app _ t) u)
        (ht.subst_congr _ _ (assigned_here hη)) (hu.subst_congr _ _ (assigned_here hη))
  | all _ ih | ex _ ih =>
      change Term.app _ (.lam ind (eval (s := prop) _ (η.extend (b := ind) (fresh ind (d ind))) (d.inc ind))) = _
      rw [ih rfl _ _ hη.extend]
      rfl

theorem normalize_individual_eq {e : Term ind} (h : Individual e) : normalize e = e := by
  change eval e ambient Depth.zero = e
  rw [individual_eval h]
  change e.subst (atDepth ambient Depth.zero) = e
  have he : atDepth ambient Depth.zero = Sub.id := by
    funext s n; cases s <;> simp [atDepth, ambient, Sub.id, Depth.zero, reflect, readback]
  rw [he, Term.subst_id]

theorem normalize_formula_eq {e : Term prop} (h : Formula e) : normalize e = e := by
  change eval e ambient Depth.zero = e
  rw [formula_eval h rfl ambient Sub.id]
  · exact e.subst_id
  · intro n k hk
    simp [ambient, Sub.id, Term.rename, Depth.weaken, Depth.zero, Nat.add_comm, reflect, readback]

/-- The normal form after first-order substitution is just the substituted syntax. -/
theorem normalize_subst_formula {e : Term prop} (h : Formula e) (σ : Sub)
    (hσ : ∀ n, Individual (σ ind n)) : normalize (e.subst σ) = e.subst σ :=
  normalize_formula_eq (h.subst σ hσ)

theorem normalize_instantiate_formula {e : Term prop} {a : Term ind}
    (he : Formula e) (ha : Individual a) : normalize (e.instantiate a) = e.instantiate a := by
  apply normalize_subst_formula he
  intro n; cases n with
  | zero => exact ha
  | succ n => exact .bound _

end Lisa.SCLambdaToPure.FirstOrderShape

