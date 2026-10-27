import Lisa.SCLambdaToPure.EmbeddingNamed

/-! The reverse interpretation preserves eigenvariable freshness. -/

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder Lambda FirstOrderShape

theorem term_free (η : Nat → Identifier) (hη : Function.Injective η)
    (t : Readback.BTerm n) (x : Nat)
    (h : SVar.mk (η x) ind ∈ (term (environment η n) t).freeVars) : x ∈ t.varFinsetLeft := by
  induction t with
  | var z =>
      cases z with
      | inl y =>
          have hxy : x = y := hη (congrArg SVar.id (Finset.mem_singleton.mp h))
          simp [hxy]
      | inr => simp [term, environment] at h
  | func c ts ih =>
      rcases mem_apps _ _ _ h with hc | ⟨i, hi⟩
      · simp at hc
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ih i hi⟩

theorem formula_free (η : Nat → Identifier) (hη : Function.Injective η)
    (p : Readback.BFormula n) (x : Nat)
    (h : SVar.mk (η x) ind ∈ (formula η p).freeVars) : x ∈ p.freeVarFinset := by
  induction p with
  | falsum => simp [formula] at h
  | equal t u =>
      simp only [formula, Term.freeVars, Finset.empty_union, Finset.mem_union] at h
      exact h.elim (fun h => Finset.mem_union_left _ (term_free η hη t x h))
        (fun h => Finset.mem_union_right _ (term_free η hη u x h))
  | @rel n a c ts =>
      rcases mem_apps _ _ _ h with hc | ⟨i, hi⟩
      · have hs : arity a prop ≠ ind := by cases a <;> simp [arity]
        simp only [head] at hc
        split at hc
        · have he := congrArg SVar.sort (Finset.mem_singleton.mp hc)
          exact False.elim (hs he.symm)
        · simp at hc
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, term_free η hη (ts i) x hi⟩
  | imp p q ihp ihq =>
      simp only [formula, Term.freeVars, Finset.empty_union, Finset.mem_union] at h
      exact h.elim (fun h => Finset.mem_union_left _ (ihp h))
        (fun h => Finset.mem_union_right _ (ihq h))
  | all p ih =>
      apply ih
      simpa [formula] using h

theorem fresh (η : Nat → Identifier) (hη : Function.Injective η)
    (x : Nat) (Γ : Pure.Context Readback.language) (hx : Pure.Fresh x Γ) :
    A.Fresh ⟨η x, ind⟩ (Γ.image (ofFormula η)) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  apply fresh_ofTyped _ (closedFormula_closed η q) ⟨η x, ind⟩
    (fun h => hx q hq (formula_free η hη q x h))
  simp [ofFormula]

end Lisa.SCLambdaToPure.Embedding
