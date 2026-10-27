import Lisa.SCLambdaToPure.ReadbackBinding
import Lisa.SCLambdaToPure.Support

/-! Substitution of a closed individual term agrees on both syntaxes. -/

namespace Lisa.SCLambdaToPure

open FirstOrder Lambda

theorem FirstOrderShape.Individual.rename_closed {e : Term s}
    (he : FirstOrderShape.Individual e) (hc : Supported Depth.zero xs e) (ρ : Ren) :
    e.rename ρ = e := by
  induction he with
  | bound => exact False.elim (Nat.not_lt_zero _ hc)
  | free | symbol => rfl
  | app _ _ ihf iha => exact congrArg₂ Term.app (ihf hc.1) (iha hc.2)

namespace Readback

private theorem closed_reads {e : Term s} (he : FirstOrderShape.Individual e)
    (hc : Supported Depth.zero xs e) (ρ : Bound n) :
    (∀ h : s = ind, term ρ (h ▸ e) = (term (fun _ => none) (h ▸ e)).map
      (Language.Term.relabel (Sum.elim Sum.inl Fin.elim0))) ∧
    (s ≠ ind → spine ρ e = (spine (fun _ => none) e).map
      (fun v => (v.1, v.2.map (Language.Term.relabel (Sum.elim Sum.inl Fin.elim0))))) := by
  induction he with
  | bound => exact False.elim (Nat.not_lt_zero _ hc)
  | free x =>
      constructor
      · intro _; simp [term]
      · simp
  | symbol a c =>
      constructor
      · intro h
        cases a with
        | zero =>
            change term ρ (.const c) = (term (n := 0) (fun _ => none) (.const c)).map _
            simp [term]
            funext i; exact i.elim0
        | succ a => cases h
      · intro _; simp [spine]
  | @app s g a _ _ ihg iha =>
      have hg := (ihg hc.1).2 (by simp)
      have ha := (iha hc.2).1 rfl
      constructor
      · intro h; subst s
        simp only [term, hg, ha]
        cases spine (n := 0) (fun _ => none) g with
        | none => rfl
        | some v =>
            obtain ⟨c, ts⟩ := v
            cases term (n := 0) (fun _ => none) a <;> simp [Language.Term.relabel]
            refine ⟨HEq.rfl, ?_⟩
            apply (Fin.heq_fun_iff (by simp)).mpr
            rintro ⟨i, hi⟩
            simp only [List.get_eq_getElem, ← List.map_singleton, ← List.map_append, List.getElem_map]
      · intro _
        simp only [spine, hg, ha]
        cases spine (n := 0) (fun _ => none) g with
        | none => rfl
        | some v =>
            obtain ⟨c, ts⟩ := v
            cases term (n := 0) (fun _ => none) a <;> simp

theorem term_closed {e : Term ind} (he : FirstOrderShape.Individual e)
    (hc : Supported Depth.zero xs e) (ρ : Bound n) :
    term ρ e = (term (fun _ => none) e).map
      (Language.Term.relabel (Sum.elim Sum.inl Fin.elim0)) := (closed_reads he hc ρ).1 rfl

theorem mapTerms_subst (k : Nat) (f : ∀ n, BTerm n → BTerm (k + n))
    (σ : Nat → Pure.Term language) (p : BFormula n) :
    mapTerms k (fun n t => f n (t.subst
      (Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i))))) p =
      mapTerms k f (p.subst σ) := by
  induction p with
  | falsum | equal | rel => rfl
  | imp p q ihp ihq => exact congrArg₂ Language.BoundedFormula.imp ihp ihq
  | all p ih => exact congrArg Language.BoundedFormula.all ih

theorem term_closed_pure {a : Term ind} (he : FirstOrderShape.Individual a)
    (hc : Supported Depth.zero xs a) {t : Pure.Term language}
    (ht : (term (fun _ => none) a).map
      (Language.Term.relabel (Sum.elim id Fin.elim0)) = some t) (ρ : Bound n) :
    term ρ a = some (t.relabel Sum.inl) := by
  rw [term_closed he hc ρ]
  cases h : term (n := 0) (fun _ => none) a <;> simp only [h, Option.map_none, Option.map_some] at ht ⊢
  · contradiction
  · cases ht
    rw [Language.Term.relabel_relabel]
    congr 2
    funext z
    cases z with
    | inl => rfl
    | inr i => exact i.elim0

def substName (x : Identifier) (t : Pure.Term language) (n : Nat) (u : BTerm n) : BTerm (0 + n) :=
  (u.subst (Sum.elim (fun y =>
    (if y = variableCode x then t else .var y).relabel Sum.inl) (fun i => .var (.inr i)))).relabel
      (Language.BoundedFormula.relabelAux (Sum.inl : Nat → Nat ⊕ Fin 0) n)

private theorem single_bound (x : Identifier) (a : Term ind) (t : Pure.Term language) (n i : Nat) :
    term (scope (0 + n)) ((Replacement.single ⟨x, ind⟩ a).bound ind i) =
      (term (scope n) (.bound i)).map (substName x t n) := by
  by_cases hi : i < n <;>
    simp [Replacement.single, Sub.id, term, scope, hi, substName,
      Language.BoundedFormula.relabelAux]

private theorem single_free (x : Identifier) (a : Term ind)
    (he : FirstOrderShape.Individual a) (hc : Supported Depth.zero xs a)
    (t : Pure.Term language)
    (ht : (term (fun _ => none) a).map
      (Language.Term.relabel (Sum.elim id Fin.elim0)) = some t)
    (n : Nat) (y : Identifier) :
    term (scope (0 + n)) ((Replacement.single ⟨x, ind⟩ a).free ind y) =
      (term (scope n) (.free y)).map (substName x t n) := by
  by_cases hy : y = x
  · subst y
    simp only [Replacement.single, ↓reduceDIte, term, Option.map_some]
    change term (scope (0 + n)) a = some (substName x t n (.var (.inl (variableCode x))))
    rw [term_closed_pure he hc ht]
    simp [substName, Language.Term.relabel_relabel,
      Language.BoundedFormula.relabelAux, Function.comp_def]
  · have hcode : variableCode y ≠ variableCode x := fun h => hy (variableCode_injective h)
    simp [Replacement.single, hy, term, substName, hcode,
      Language.BoundedFormula.relabelAux]

theorem formula_single {e : Term prop} {p : BFormula 0}
    (hp : formula (fun _ => none) e = some p) (x : Identifier) (a : Term ind)
    (he : FirstOrderShape.Individual a) (hc : Supported Depth.zero xs a)
    {t : Pure.Term language}
    (ht : (term (fun _ => none) a).map
      (Language.Term.relabel (Sum.elim id Fin.elim0)) = some t) :
    formula (fun _ => none) ((Replacement.single ⟨x, ind⟩ a).apply e) =
      some (Pure.substOne (variableCode x) t p) := by
  have h := formula_replace 0 (fun _ => Replacement.single ⟨x, ind⟩ a)
    (fun _ => single_heads x a) (fun _ => (single_lift x a (he.rename_closed hc _)).symm)
    scope (fun n => scope (0 + n)) scope_succ (fun n => scope_succ (0 + n))
    (substName x t) (by intros; rfl) (single_bound x a t) (single_free x a he hc t ht)
    0 (fun _ => none) e (by simp) hp
  have hm : mapTerms 0 (substName x t) p =
      (p.subst (fun y => if y = variableCode x then t else .var y)).relabel
        (Sum.inl : Nat → Nat ⊕ Fin 0) :=
    (mapTerms_subst 0
      (fun n u => u.relabel (Language.BoundedFormula.relabelAux Sum.inl n)) _ p).trans
        (mapTerms_relabel _ _)
  rw [hm] at h
  simpa [Pure.substOne] using h

end Readback
end Lisa.SCLambdaToPure
