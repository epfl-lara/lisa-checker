import Lisa.SCLambdaToPure.BoundaryLogic

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder Lambda

theorem subst_self (x : SVar) (p : Expr) (hp : isFormula p) (hx : x.sort = ind) :
    A.ofExpr (Expr.substOne x (.var x) p) (isFormula_substOne hx (congrArg some hx) hp) =
      A.ofExpr p hp := by
  apply (A.ofExpr_eq _ _).mpr
  apply AlphaBetaEta.alpha
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  apply alpha_of_interpretNamed_eq _ he
  rw [show interpretNamed (Expr.substOne x (.var x) p) Names.free = interpretNamed p Names.free from ?_]
  · exact he
  apply interpretNamed_namedSubst
  intro y _
  simp only [NamedSubst.lookup_insert, Lean.AssocList.find?]
  by_cases h : y = x
  · subst y; simp [interpretNamed, Names.free]
  · simp [h]

theorem fresh_all (x : Identifier) (p : Expr) (hp : isFormula p) :
    A.Fresh ⟨x, ind⟩ {A.ofExpr (Expr.forall_ ⟨x, ind⟩ p) (isFormula_forall rfl hp)} := by
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  exact ⟨_, _, rfl, by simp [Expr.forall_, Expr.freeVars]⟩

theorem fresh_ex (x : Identifier) (p : Expr) (hp : isFormula p) :
    A.Fresh ⟨x, ind⟩ {A.ofExpr (Expr.exists_ ⟨x, ind⟩ p) (isFormula_exists rfl hp)} := by
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  exact ⟨_, _, rfl, by simp [Expr.exists_, Expr.freeVars]⟩

private theorem pure_subst_self (x : Nat) (p : Pure.Formula Readback.language) :
    Pure.substOne x (.var x) p = p := by
  unfold Pure.substOne
  have h : (fun y => if y = x then Language.Term.var x else Language.Term.var y) =
      (Language.Term.var : Nat → Pure.Term Readback.language) := by
    funext y; split <;> simp_all
  rw [h]
  have ht {α : Type} (t : Readback.language.Term α) : t.subst Language.Term.var = t := by
    induction t with
    | var => rfl
    | func c ts ih => simp [Language.Term.subst, ih]
  have hn (n : Nat) :
      Sum.elim (Language.Term.relabel Sum.inl ∘ (Language.Term.var : Nat → Pure.Term Readback.language))
        (Language.Term.var ∘ (Sum.inr : Fin n → Nat ⊕ Fin n)) = Language.Term.var := by
    funext y; cases y <;> rfl
  simp only [Language.BoundedFormula.subst, hn]
  have he : (fun n (t : Readback.BTerm n) => t.subst Language.Term.var) = (fun _ => id) := by
    funext n t; exact ht t
  rw [he, Language.BoundedFormula.mapTermRel_id_id_id]

private theorem fresh_exists_pure (x : Nat) (p : Pure.Formula Readback.language) :
    Pure.Fresh x {Pure.exists_ x p} := by
  let g : Nat → Nat ⊕ Fin 1 := fun y => if y = x then .inr 0 else .inl y
  have ht (n : Nat) (t : Readback.BTerm n) :
      x ∉ (t.relabel (Language.BoundedFormula.relabelAux g n)).varFinsetLeft := by
    induction t with
    | var y =>
        cases y with
        | inl y => by_cases h : y = x <;>
            simp [Language.Term.relabel, Language.Term.varFinsetLeft,
              Language.BoundedFormula.relabelAux, g, h, Ne.symm]
        | inr i => simp [Language.Term.relabel, Language.Term.varFinsetLeft,
            Language.BoundedFormula.relabelAux]
    | func c ts ih => simpa [Language.Term.relabel, Language.Term.varFinsetLeft] using ih
  have hf {n : Nat} (q : Readback.BFormula n) :
      x ∉ (Readback.mapTerms 1 (fun n t => t.relabel (Language.BoundedFormula.relabelAux g n)) q).freeVarFinset := by
    induction q with
    | falsum => simp [Readback.mapTerms, Language.BoundedFormula.freeVarFinset]
    | equal t u => simp [Readback.mapTerms, Language.BoundedFormula.freeVarFinset, ht]
    | rel c ts => simp [Readback.mapTerms, Language.BoundedFormula.freeVarFinset, ht]
    | imp p q ihp ihq => simp [Readback.mapTerms, Language.BoundedFormula.freeVarFinset, ihp, ihq]
    | all p ih => simpa [Readback.mapTerms, Language.BoundedFormula.freeVarFinset] using ih
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  simpa [Readback.mapTerms_relabel, g, Pure.exists_, Pure.bind,
    Language.BoundedFormula.ex, Language.BoundedFormula.not,
    Language.BoundedFormula.freeVarFinset] using hf p

namespace Related

variable {η : Nat → Identifier} {p : Expr} {hp : isFormula p}
  {p' : Pure.Formula Readback.language}

noncomputable def all (hη : Function.Injective η) (x : Identifier)
    (hx : η (Readback.variableCode x) = x) (h : Related η (A.ofExpr p hp) p') :
    Related η (A.ofExpr (Expr.forall_ ⟨x, ind⟩ p) (isFormula_forall rfl hp))
      (Pure.forall_ (Readback.variableCode x) p') := by
  constructor
  · apply rightAll (Δ := ∅) hη
    · apply A.ProofTree.leftForall (Γ := ∅) ⟨x, ind⟩ p (.var ⟨x, ind⟩) rfl hp rfl
      simpa only [subst_self ⟨x, ind⟩ p hp rfl, Finset.insert_empty] using h.forward
    · simpa only [hx] using fresh_all x p hp
    · intro q hq; simp at hq
  · apply A.ProofTree.rightForall (Δ := ∅) ⟨x, ind⟩ p rfl hp
    · apply leftAll (Γ := ∅) hη (Readback.variableCode x) p' (.var (Readback.variableCode x))
      simpa only [pure_subst_self, Finset.insert_empty] using h.backward
    · rw [ofFormula_all η hη, hx]
      exact fresh_all x _ (namedFormula_sort η p')
    · intro q hq; simp at hq

noncomputable def ex (hη : Function.Injective η) (x : Identifier)
    (hx : η (Readback.variableCode x) = x) (h : Related η (A.ofExpr p hp) p') :
    Related η (A.ofExpr (Expr.exists_ ⟨x, ind⟩ p) (isFormula_exists rfl hp))
      (Pure.exists_ (Readback.variableCode x) p') := by
  constructor
  · apply A.ProofTree.leftExists (Γ := ∅) ⟨x, ind⟩ p rfl hp
    · apply rightExists (Δ := ∅) hη (Readback.variableCode x) p' (.var (Readback.variableCode x))
      simpa only [pure_subst_self, Finset.insert_empty] using h.forward
    · intro q hq; simp at hq
    · simpa only [Finset.image_singleton, hx] using
        fresh η hη (Readback.variableCode x) _ (fresh_exists_pure (Readback.variableCode x) p')
  · apply leftExists (Γ := ∅) hη (Readback.variableCode x) p'
    · apply A.ProofTree.rightExists (Δ := ∅) ⟨x, ind⟩ p (.var ⟨x, ind⟩) rfl hp rfl
      simpa only [subst_self ⟨x, ind⟩ p hp rfl, Finset.insert_empty] using h.backward
    · intro q hq; simp at hq
    · simpa only [hx] using fresh_ex x p hp

end Related
end Lisa.SCLambdaToPure.Embedding
