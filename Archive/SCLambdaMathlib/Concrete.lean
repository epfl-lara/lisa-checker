import Lisa.SCLambdaToPure.AToPure
import Lisa.SCLambdaToPure.TranslationSubstitution

/-! Translating A proofs using the verified, concrete normalization pipeline. -/

namespace Lisa.SCLambdaToPure.Translation

open FirstOrder

@[simp] theorem term_var (x : SVar) (hx : x.sort = ind) :
    term (.var x) (congrArg some hx) = .var (Readback.variableCode x.id) := by
  obtain ⟨x, s⟩ := x
  cases hx
  apply term_eq_of_read
  simp [readTerm, normalized, Lambda.interpretNamed, Lambda.Names.free,
    Grounding.ground, Grounding.symbols, Grounding.Symbols.apply, Grounding.free,
    Lambda.normalize, Lambda.quote, Lambda.reflect, Lambda.readback, Readback.term]

/-- Every law in the transport interface is discharged by the concrete reader. -/
def interpretation : A.Interpretation Readback.language where
  formula := formula
  term := term
  name x := Readback.variableCode x.id
  bot := formula_bot
  top := formula_top
  and := formula_and
  or := formula_or
  imp := formula_imp
  iff := formula_iff
  neg := formula_neg
  eq := formula_eq
  subst := formula_subst
  all := formula_all
  ex := formula_ex
  fresh := fresh

noncomputable def context (Γ : A.Context) : Pure.Context Readback.language := Γ.image formula

/-- Translate a proof over a fixed theory once its axioms have been translated.
There is no assumed interpretation law or restriction on intermediate formulas. -/
noncomputable def toPureWithAxioms {T : A.Theory} {U : Readback.language.Theory}
    (axioms : ∀ p ∈ T, Pure.ProofTree U ∅ {formula p})
    {Γ Δ : A.Context} (d : A.ProofTree T Γ Δ) :
    Pure.ProofTree U (context Γ) (context Δ) := interpretation.toPure axioms d

/-- The concrete proof translation for sequents with arbitrary assumptions.
Higher-order symbols are allowed anywhere in the input proof. -/
noncomputable def toPure {Γ Δ : A.Context} (d : A.ProofTree ∅ Γ Δ) :
    Pure.ProofTree ∅ (context Γ) (context Δ) :=
  toPureWithAxioms (fun _ h => False.elim h) d

theorem provable_toPure {Γ Δ : A.Context} (h : A.Provable ∅ Γ Δ) :
    Pure.Provable ∅ (context Γ) (context Δ) := by
  obtain ⟨d⟩ := h
  exact ⟨toPure d⟩

end Lisa.SCLambdaToPure.Translation
