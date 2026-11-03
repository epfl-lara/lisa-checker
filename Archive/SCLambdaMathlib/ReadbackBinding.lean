import Lisa.SCLambdaToPure.Bridge
import Lisa.SCLambdaToPure.ReadbackReplacement

/-! Named abstraction agrees with Mathlib's locally nameless quantifiers. -/

namespace Lisa.SCLambdaToPure.Readback

open FirstOrder Lambda

def bindName (x : Identifier) (y : Nat) : Nat ⊕ Fin 1 :=
  if y = variableCode x then .inr 0 else .inl y

theorem mapTerms_relabel (g : Nat → Nat ⊕ Fin k) (p : BFormula n) :
    mapTerms k (fun n t => t.relabel (Language.BoundedFormula.relabelAux g n)) p = p.relabel g := by
  induction p with
  | falsum | equal | rel => rfl
  | imp p q ihp ihq => simp [mapTerms, ihp, ihq]
  | all p ih => simp [mapTerms, ih]

private theorem abstractAt_bound (x : Identifier) (n i : Nat) :
    term (scope (1 + n)) ((abstractAt x n).bound ind i) =
      (term (scope n) (.bound i)).map
        (Language.Term.relabel (Language.BoundedFormula.relabelAux (bindName x) n)) := by
  by_cases hi : i < n
  · simp [abstractAt, term, scope, hi, show ¬n ≤ i by omega,
      Language.BoundedFormula.relabelAux]
    omega
  · simp [abstractAt, term, scope, hi, show n ≤ i by omega, show ¬i + 1 < 1 + n by omega]

private theorem abstractAt_free (x y : Identifier) (n : Nat) :
    term (scope (1 + n)) ((abstractAt x n).free ind y) =
      (term (scope n) (.free y)).map
        (Language.Term.relabel (Language.BoundedFormula.relabelAux (bindName x) n)) := by
  by_cases h : y = x
  · subst y
    simp [abstractAt, term, scope, Language.BoundedFormula.relabelAux, bindName]
    rfl
  · have hc : variableCode y ≠ variableCode x := fun he => h (variableCode_injective he)
    simp [abstractAt, h, term, Language.BoundedFormula.relabelAux, bindName, hc]

theorem formula_abstract {e : Term prop} {p : BFormula 0}
    (hp : formula (fun _ => none) e = some p) (x : Identifier) :
    formula (bind (fun _ => none)) ((Replacement.abstract ⟨x, ind⟩).apply e) =
      some (Pure.bind (variableCode x) p) := by
  have h := formula_replace 1 (abstractAt x) (abstractAt_heads x) (abstractAt_lift x)
    scope (fun n => scope (1 + n)) scope_succ (fun n => scope_succ (1 + n))
    (fun n t => t.relabel (Language.BoundedFormula.relabelAux (bindName x) n))
    (by intros; rfl) (abstractAt_bound x) (fun n y => abstractAt_free x y n)
    0 (fun _ => none) e (by simp) hp
  simpa [abstractAt_zero, scope_succ, mapTerms_relabel, Pure.bind, bindName] using h

end Lisa.SCLambdaToPure.Readback
