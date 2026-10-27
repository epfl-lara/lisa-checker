import Lisa.SCLambdaToPure.Embedding

/-! Reifying the typed embedding gives representatives of A's formula classes. -/

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder Lambda

def ofTyped (e : Term s) : A.Expression s := A.ofExpr (e.reify Context.empty) (e.reify_sort _)

def namedFormula (η : Nat → Identifier) (p : Pure.Formula Readback.language) : Expr :=
  (closedFormula η p).reify Context.empty

def namedTerm (η : Nat → Identifier) (t : Pure.Term Readback.language) : Expr :=
  (closedTerm η t).reify Context.empty

def ofFormula (η : Nat → Identifier) (p : Pure.Formula Readback.language) : A.Formula :=
  ofTyped (closedFormula η p)

theorem namedFormula_sort (η : Nat → Identifier) (p : Pure.Formula Readback.language) :
    isFormula (namedFormula η p) := (closedFormula η p).reify_sort _

theorem namedTerm_sort (η : Nat → Identifier) (t : Pure.Term Readback.language) :
    isTerm (namedTerm η t) := (closedTerm η t).reify_sort _

theorem interpret_namedFormula (η : Nat → Identifier) (p : Pure.Formula Readback.language) :
    interpretNamed (namedFormula η p) Names.free = some ⟨prop, closedFormula η p⟩ := by
  simp [namedFormula, closedFormula_closed]

theorem interpret_namedTerm (η : Nat → Identifier) (t : Pure.Term Readback.language) :
    interpretNamed (namedTerm η t) Names.free = some ⟨ind, closedTerm η t⟩ := by
  simp [namedTerm, closedTerm_closed]

@[simp] theorem ofFormula_bot (η : Nat → Identifier) : ofFormula η ⊥ = A.ofExpr Expr.bot rfl := rfl

theorem ofFormula_imp (η : Nat → Identifier) (p q : Pure.Formula Readback.language) :
    ofFormula η (p.imp q) = A.ofExpr (Expr.imp (namedFormula η p) (namedFormula η q))
      (isFormula_imp (namedFormula_sort η p) (namedFormula_sort η q)) := rfl

theorem ofFormula_equal (η : Nat → Identifier) (t u : Pure.Term Readback.language) :
    ofFormula η (t.equal u) = A.ofExpr (Expr.eq (namedTerm η t) (namedTerm η u))
      (isFormula_eq (namedTerm_sort η t) (namedTerm_sort η u)) := by
  change ofTyped (.app (.app (.const ⟨"eq", 0⟩)
    (term (environment η 0) (t.relabel Sum.inl)))
    (term (environment η 0) (u.relabel Sum.inl))) = _
  simp only [term_relabel]
  rfl

theorem ofFormula_all (η : Nat → Identifier) (hη : Function.Injective η)
    (x : Nat) (p : Pure.Formula Readback.language) :
    ofFormula η (Pure.forall_ x p) = A.ofExpr (Expr.forall_ ⟨η x, ind⟩ (namedFormula η p))
      (isFormula_forall rfl (namedFormula_sort η p)) := by
  apply (A.ofExpr_eq _ _).mpr
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_namedFormula η (Pure.forall_ x p))
  simp [Expr.forall_, interpretNamed, Replacement.interpretNamed_bind,
    interpret_namedFormula, Packed.app, Packed.lam, Replacement.packed,
    closedFormula, Pure.forall_, formula, formula_bind η hη]

theorem ofFormula_subst (η : Nat → Identifier) (hη : Function.Injective η)
    (x : Nat) (t : Pure.Term Readback.language) (p : Pure.Formula Readback.language) :
    ofFormula η (Pure.substOne x t p) =
      A.ofExpr (Expr.substOne ⟨η x, ind⟩ (namedTerm η t) (namedFormula η p))
        (isFormula_substOne rfl (namedTerm_sort η t) (namedFormula_sort η p)) := by
  apply (A.ofExpr_eq _ _).mpr
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq (interpret_namedFormula η (Pure.substOne x t p))
  rw [interpretNamed_substOne _ _ _ _ _ (interpret_namedTerm η t),
    Replacement.interpretNamed_bind, interpret_namedFormula]
  simp only [Option.map_some, Packed.subst, Replacement.packed]
  change some (⟨prop, ((Replacement.abstract ⟨η x, ind⟩).apply (closedFormula η p)).instantiate
    (closedTerm η t)⟩ : Packed.Expr) = _
  rw [Replacement.instantiate_abstract]
  simp only [closedFormula, formula_substOne η hη]

theorem ofTyped_eq_of_closed (e : Term s) (hc : ∀ σ, e.subst σ = e) (ρ : Context) :
    A.ofExpr (e.reify ρ) (e.reify_sort ρ) = ofTyped e := by
  apply (A.ofExpr_eq _ _).mpr
  apply AlphaBetaEta.alpha
  apply alpha_of_interpretNamed_eq
    (show interpretNamed (e.reify ρ) Names.free = some ⟨s, e⟩ by simp [hc])
    (show interpretNamed (e.reify Context.empty) Names.free = some ⟨s, e⟩ by simp [hc])

/-- A fresh representative can be chosen without relying on the arbitrary
ambient-name convention of `Context.empty`. -/
theorem fresh_ofTyped (e : Term prop) (hc : ∀ σ, e.subst σ = e) (x : SVar)
    (hx : x ∉ e.freeVars) : A.Fresh x {ofTyped e} := by
  intro p hp
  obtain rfl := Finset.mem_singleton.mp hp
  let c := freshId {x.id} ⟨"_unused", 0⟩
  let ρ : Context := ⟨fun _ _ => c, fun _ => {c}, by simp⟩
  refine ⟨e.reify ρ, e.reify_sort ρ, ofTyped_eq_of_closed e hc ρ, ?_⟩
  intro h
  rcases e.reify_freeVars ρ x h with h | h
  · exact hx h
  · have he : x.id = c := Finset.mem_singleton.mp h
    exact freshId_not_mem {x.id} ⟨"_unused", 0⟩ (by simp [c, ← he])

end Lisa.SCLambdaToPure.Embedding

