import Lisa.SCLambdaToPure.Bridge
import Lisa.SCLambdaToPure.Concrete

/-! Embedding Mathlib first-order expressions into intrinsically sorted lambda
expressions. Only the individual sort is bound by first-order quantifiers. -/

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder Lambda FirstOrderShape

def term (v : α → Term ind) : Readback.language.Term α → Term ind
  | .var x => v x
  | .func (l := n) c ts => apps n (.const c.id) (fun i => term v (ts i))

theorem term_relabel (v : β → Term ind) (f : α → β) (t : Readback.language.Term α) :
    term v (t.relabel f) = term (v ∘ f) t := by
  induction t with
  | var => rfl
  | func c ts ih => simp only [Language.Term.relabel, term]; congr 1; funext i; exact ih i

theorem term_subst (v : β → Term ind) (σ : α → Readback.language.Term β)
    (t : Readback.language.Term α) : term v (t.subst σ) = term (fun x => term v (σ x)) t := by
  induction t with
  | var => rfl
  | func c ts ih => simp only [Language.Term.subst, term]; congr 1; funext i; exact ih i

theorem term_replace (R : Replacement)
    (hh : ∀ s c, R.const s c = .const c)
    (v : α → Term ind) (t : Readback.language.Term α) :
    R.apply (term v t) = term (fun x => R.apply (v x)) t := by
  induction t with
  | var => rfl
  | func c ts ih =>
      simp only [term, apps_replace, Replacement.apply, hh]
      congr 1; funext i; exact ih i

/-- Mathlib levels count from the outside, Lisa indices from the nearest binder. -/
def environment (η : Nat → Identifier) (n : Nat) : Nat ⊕ Fin n → Term ind
  | .inl x => .free (η x)
  | .inr i => .bound (n - 1 - i.val)

def formula (η : Nat → Identifier) : {n : Nat} → Readback.BFormula n → Term prop
  | _, .falsum => .const ⟨"bot", 0⟩
  | n, .equal t u =>
      .app (.app (.const ⟨"eq", 0⟩) (term (environment η n) t)) (term (environment η n) u)
  | n, .rel (l := a) c ts =>
      apps a (head c (arity a prop)) (fun i => term (environment η n) (ts i))
  | _, .imp p q => .app (.app (.const ⟨"imp", 0⟩) (formula η p)) (formula η q)
  | _, .all p => .app (.const ⟨"forall", 0⟩) (.lam ind (formula η p))

def closedFormula (η : Nat → Identifier) (p : Pure.Formula Readback.language) : Term prop :=
  formula η p

def closedTerm (η : Nat → Identifier) (t : Pure.Term Readback.language) : Term ind :=
  term (fun x => .free (η x)) t

private theorem head_replace (R : Replacement) (hR : Readback.PreservesHeads R)
    (c : Readback.Symbol) (a : Nat) : R.apply (head c (arity a prop)) = head c (arity a prop) := by
  have hs : arity a prop ≠ ind := by cases a <;> simp [arity]
  simp only [head]
  split
  · exact hR.free _ hs _
  · exact hR.const _ _

/-- A common compatibility lemma for both binding and individual substitution. -/
theorem formula_mapTerms (η : Nat → Identifier) (k : Nat) (R : Nat → Replacement)
    (hR : ∀ n, Readback.PreservesHeads (R n)) (hl : ∀ n, R (n + 1) = (R n).lift ind)
    (f : ∀ n, Readback.BTerm n → Readback.BTerm (k + n))
    (ht : ∀ n t, term (environment η (k + n)) (f n t) = (R n).apply (term (environment η n) t))
    (p : Readback.BFormula n) : formula η (Readback.mapTerms k f p) = (R n).apply (formula η p) := by
  induction p with
  | falsum => exact ((hR _).const _ _).symm
  | equal => simp [Readback.mapTerms, formula, Replacement.apply, (hR _).const, ht]
  | rel c ts =>
      simp only [Readback.mapTerms, formula, apps_replace, head_replace _ (hR _), ht]
  | imp p q ihp ihq => simp [Readback.mapTerms, formula, Replacement.apply, (hR _).const, ihp, ihq]
  | all p ih =>
      simp only [Readback.mapTerms, formula, Replacement.apply, (hR _).const, ih, hl]

theorem formula_bind (η : Nat → Identifier) (hη : Function.Injective η)
    (x : Nat) (p : Pure.Formula Readback.language) :
    formula η (Pure.bind x p) = (Replacement.abstract ⟨η x, ind⟩).apply (formula η p) := by
  let g : Nat → Nat ⊕ Fin 1 := fun y => if y = x then .inr 0 else .inl y
  have ht (n : Nat) (t : Readback.BTerm n) :
      term (environment η (1 + n)) (t.relabel (Language.BoundedFormula.relabelAux g n)) =
        (Readback.abstractAt (η x) n).apply (term (environment η n) t) := by
    rw [term_relabel, term_replace _ (by intros; rfl)]
    congr 1
    funext z
    cases z with
    | inl y =>
        by_cases hy : y = x
        · subst y; simp [g, Function.comp_def, Language.BoundedFormula.relabelAux,
            environment, Readback.abstractAt, Replacement.apply]
        · have hne : η y ≠ η x := fun h => hy (hη h)
          simp [g, hy, hne, Function.comp_def, Language.BoundedFormula.relabelAux,
            environment, Readback.abstractAt, Replacement.apply]
    | inr i =>
        simp [Function.comp_def, Language.BoundedFormula.relabelAux,
          environment, Readback.abstractAt, Replacement.apply, show ¬n ≤ n - 1 - i.val by omega]
        omega
  have h := formula_mapTerms η 1 (Readback.abstractAt (η x)) (Readback.abstractAt_heads (η x))
    (Readback.abstractAt_lift (η x))
    (fun n t => t.relabel (Language.BoundedFormula.relabelAux g n)) ht p
  simpa [Readback.mapTerms_relabel, Readback.abstractAt_zero, Pure.bind, g] using h

theorem term_scoped (η : Nat → Identifier) (t : Readback.BTerm n) (σ : Sub)
    (hσ : ∀ i < n, σ ind i = .bound i) :
    (term (environment η n) t).subst σ = term (environment η n) t := by
  rw [← Replacement.apply_ofSub, term_replace _ (by intros; rfl)]
  congr 1
  funext z
  cases z with
  | inl => rfl
  | inr i => exact hσ _ (by omega)

theorem formula_scoped (η : Nat → Identifier) (p : Readback.BFormula n) (σ : Sub)
    (hσ : ∀ i < n, σ ind i = .bound i) : (formula η p).subst σ = formula η p := by
  induction p generalizing σ with
  | falsum => rfl
  | equal t u => simp [formula, Term.subst, term_scoped η t σ hσ, term_scoped η u σ hσ]
  | rel c ts =>
      simp only [formula, ← Replacement.apply_ofSub, apps_replace]
      simp only [Replacement.apply_ofSub]
      have hh (s : LSort) : (head c s).subst σ = head c s := by
        simp only [head]; split <;> rfl
      rw [hh]
      congr 1
      funext i
      exact term_scoped η (ts i) σ hσ
  | imp p q ihp ihq => simp [formula, Term.subst, ihp σ hσ, ihq σ hσ]
  | all p ih =>
      simp only [formula, Term.subst]
      congr 2
      apply ih
      intro i hi
      cases i with
      | zero => simp
      | succ i => simp [hσ i (by omega), Term.shift, Term.rename, Ren.shift]

theorem closedFormula_closed (η : Nat → Identifier) (p : Pure.Formula Readback.language) (σ : Sub) :
    (closedFormula η p).subst σ = closedFormula η p := formula_scoped η p σ (by simp)

theorem closedTerm_closed (η : Nat → Identifier) (t : Pure.Term Readback.language) (σ : Sub) :
    (closedTerm η t).subst σ = closedTerm η t := by
  unfold closedTerm
  rw [← Replacement.apply_ofSub, term_replace _ (by intros; rfl)]
  rfl

theorem formula_substOne (η : Nat → Identifier) (hη : Function.Injective η)
    (x : Nat) (t : Pure.Term Readback.language) (p : Pure.Formula Readback.language) :
    formula η (Pure.substOne x t p) =
      (Replacement.single ⟨η x, ind⟩ (closedTerm η t)).apply (formula η p) := by
  let σ : Nat → Pure.Term Readback.language := fun y => if y = x then t else .var y
  let f (n : Nat) (u : Readback.BTerm n) : Readback.BTerm (0 + n) :=
    (u.subst (Sum.elim (fun y => (σ y).relabel Sum.inl) (fun i => .var (.inr i)))).relabel
      (Language.BoundedFormula.relabelAux (Sum.inl : Nat → Nat ⊕ Fin 0) n)
  let R := Replacement.single ⟨η x, ind⟩ (closedTerm η t)
  have ha : (closedTerm η t).shift ind = closedTerm η t := by
    simpa only [Term.subst_ofRen] using closedTerm_closed η t (Sub.ofRen (Ren.shift ind))
  have ht (n : Nat) (u : Readback.BTerm n) :
      term (environment η (0 + n)) (f n u) = R.apply (term (environment η n) u) := by
    simp only [f, term_relabel, term_subst, term_replace R (by intros; rfl)]
    congr 1
    funext z
    cases z with
    | inl y =>
        simp only [Sum.elim_inl, term_relabel]
        have hv : (environment η (0 + n) ∘
            Language.BoundedFormula.relabelAux (Sum.inl : Nat → Nat ⊕ Fin 0) n) ∘ Sum.inl =
            fun y => Term.free (s := ind) (η y) := by
          funext y; rfl
        rw [hv]
        by_cases hy : y = x
        · subst y; simp [σ, R, Replacement.single, Replacement.apply, environment, closedTerm]
        · have hn : η y ≠ η x := fun h => hy (hη h)
          simp [σ, hy, hn, R, Replacement.single, Replacement.apply, environment, term]
    | inr i => simp [term, Function.comp_def, Language.BoundedFormula.relabelAux,
        R, Replacement.single, Replacement.apply, environment, Sub.id]
  have h := formula_mapTerms η 0 (fun _ => R) (fun _ => Readback.single_heads _ _)
    (fun _ => (Readback.single_lift _ _ ha).symm) f ht p
  have hm : Readback.mapTerms 0 f p = (p.subst σ).relabel (Sum.inl : Nat → Nat ⊕ Fin 0) :=
    (Readback.mapTerms_subst 0
      (fun n u => u.relabel (Language.BoundedFormula.relabelAux Sum.inl n)) σ p).trans
      (Readback.mapTerms_relabel _ _)
  rw [hm] at h
  simpa [Pure.substOne, σ] using h

end Lisa.SCLambdaToPure.Embedding

