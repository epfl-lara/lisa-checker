import Lisa.OrderedEncoding
import Lisa.OrderSimulation

open Lisa Expr

namespace Ordered

/-- Each source comparison between formulas has a two-formula target derivation. -/
def Admissible (source target : ExprRel) : Type :=
  ∀ a b, isFormula a → isFormula b → source a b → ProofTree target {a} {b}

private abbrev Transport (source target : ExprRel) :=
  ∀ {Γ Δ Γ' Δ' : Finset Expr},
    isFSet Γ → isFSet Δ → isFSet Γ' → isFSet Δ' →
    sequentLeq source Γ Δ Γ' Δ' →
    ProofTree target Γ Δ → ProofTree target Γ' Δ'

/-- Pack the premise, cut with the supplied two-formula proof, then unpack the conclusion. -/
private noncomputable def transportOfAdmissible {source target : ExprRel}
    (h : Admissible source target) : Transport source target := by
  intro Γ Δ Γ' Δ' hΓ hΔ hΓ' hΔ' hab pf
  have ha := sequentToFormula_sorted hΓ hΔ
  have hb := sequentToFormula_sorted hΓ' hΔ'
  have first := ProofTree.cut (Γ := ∅) (Δ := ∅) (Ω := ∅) (Ξ := {sequentToFormula Γ' Δ'})
    (sequentToFormula Γ Δ) (by simp [isFSet]) (by simp [isFSet])
    (by simp [isFSet]) (by simpa [isFSet] using hb) ha
    (packSequent hΓ hΔ pf) (h _ _ ha hb hab)
  have second := ProofTree.cut (Γ := ∅) (Δ := ∅) (Ω := Γ') (Ξ := Δ')
    (sequentToFormula Γ' Δ') (by simp [isFSet]) (by simp [isFSet]) hΓ' hΔ' hb
    (by simpa using first) (useSequentFormula hΓ' hΔ')
  simpa using second

/-- Translate a derivation by replacing each comparison step with its supplied proof. -/
private def translateWith {source target : ExprRel} {Γ Δ}
    (hclosed : Transport source target) :
    Ordered.ProofTree source Γ Δ →
    Ordered.ProofTree target Γ Δ
  | .weakening hΓ hΔ hΓ' hΔ' pf hsubΓ hsubΔ =>
      .weakening hΓ hΔ hΓ' hΔ' (translateWith hclosed pf) hsubΓ hsubΔ
  | .rightTrue => .rightTrue
  | .leftFalse => .leftFalse
  | .restateWeaken hΓ hΔ hΓ' hΔ' pf hle =>
      hclosed hΓ hΔ hΓ' hΔ' hle (translateWith hclosed pf)
  | .hypothesis φ hφ =>
      .hypothesis φ hφ
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      .cut φ hΓ hΔ hΩ hΞ hφ (translateWith hclosed pf₁) (translateWith hclosed pf₂)
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      .leftAnd φ ψ hΓ hΔ hφ hψ (translateWith hclosed pf)
  | .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .leftOr φ ψ hΓ hΔ hΩ hΞ hφ hψ (translateWith hclosed pf₁) (translateWith hclosed pf₂)
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ (translateWith hclosed pf₁) (translateWith hclosed pf₂)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      .leftIff φ ψ hΓ hΔ hφ hψ (translateWith hclosed pf)
  | .leftNot φ hΓ hΔ hφ pf =>
      .leftNot φ hΓ hΔ hφ (translateWith hclosed pf)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      .leftForall x φ t hΓ hΔ hx hφ ht (translateWith hclosed pf)
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      .leftExists x φ hΓ hΔ hx hφ (translateWith hclosed pf) hfree
  | .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightAnd φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (translateWith hclosed pf₁) (translateWith hclosed pf₂)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      .rightOr φ ψ hΓ hΔ hφ hψ (translateWith hclosed pf)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      .rightImp φ ψ hΓ hΔ hφ hψ (translateWith hclosed pf)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ
        (translateWith hclosed pf₁) (translateWith hclosed pf₂)
  | .rightNot φ hΓ hΔ hφ pf =>
      .rightNot φ hΓ hΔ hφ (translateWith hclosed pf)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      .rightForall x φ hΓ hΔ hx hφ (translateWith hclosed pf) hfree
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      .rightExists x φ t hΓ hΔ hx hφ ht (translateWith hclosed pf)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      .rightEpsilon x φ t hΓ hΔ hx hφ ht (translateWith hclosed pf)
  | .leftRefl t hΓ hΔ ht pf =>
      .leftRefl t hΓ hΔ ht (translateWith hclosed pf)
  | .rightRefl t ht =>
      .rightRefl t ht
  | .leftSubst r hΓ hΔ hΘ hΞ hv hf p q =>
      .leftSubst r hΓ hΔ hΘ hΞ hv hf (translateWith hclosed p) (translateWith hclosed q)
  | .rightSubst r hΓ hΔ hΘ hΞ hv hf p q =>
      .rightSubst r hΓ hΔ hΘ hΞ hv hf (translateWith hclosed p) (translateWith hclosed q)
  | .instSchema σ hΓ hΔ hσ pf =>
      .instSchema σ hΓ hΔ hσ (translateWith hclosed pf)

/-- Translate using only two-formula admissibility. -/
noncomputable def translate {source target : ExprRel} (h : Admissible source target)
    {Γ Δ} (pf : ProofTree source Γ Δ) : ProofTree target Γ Δ :=
  translateWith (transportOfAdmissible h) pf

/-- Relation inclusion directly transports comparison steps; it does not need
to establish the stronger two-formula admissibility condition. -/
def mapOrder {source target : ExprRel} (sim : Subrelation source target)
    {Γ Δ} (pf : ProofTree source Γ Δ) : ProofTree target Γ Δ :=
  translateWith (fun hΓ hΔ hΓ' hΔ' h p =>
    .restateWeaken hΓ hΔ hΓ' hΔ' p (sim.sequent h)) pf

/-- Two Ordered instances prove the same sequents when each comparison rule
is admissible in the other system. -/
theorem provable_iff {source target : ExprRel}
    (forward : Admissible source target) (backward : Admissible target source)
    (Γ Δ : Finset Expr) :
    Nonempty (ProofTree source Γ Δ) ↔ Nonempty (ProofTree target Γ Δ) := by
  constructor <;> rintro ⟨pf⟩
  · exact ⟨translate forward pf⟩
  · exact ⟨translate backward pf⟩

/-- For an extension of a baseline relation, only reverse admissibility
remains to be proved. -/
theorem provable_iff_of_simulation {source target : ExprRel}
    (sim : Subrelation source target) (backward : Admissible target source)
    (Γ Δ : Finset Expr) :
    Nonempty (ProofTree source Γ Δ) ↔ Nonempty (ProofTree target Γ Δ) :=
by
  constructor <;> rintro ⟨pf⟩
  · exact ⟨mapOrder sim pf⟩
  · exact ⟨translate backward pf⟩

end Ordered
