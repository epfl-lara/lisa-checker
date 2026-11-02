import Lisa.LambdaFol.ToPureFol.PureFolToOrdered.Roundtrip
import Lisa.LambdaFol.ToPureFol.PureFolToOrdered.TranslateProof
import Lisa.LambdaFol.ToPureFol.FirstOrderConclusions

/-! Translating a first-order-compatible formula to PureFol and embedding it back
recovers its αβη class. `OrderedAlphaBetaEta.ofPureFol` uses this fact to recover
the original conclusion from an embedded PureFol proof. -/
namespace Lisa.LambdaFol.PureFolTranslation
open AlphaBetaEtaNormalization
open FirstOrderShape (AllowedConstants)

/-- Canonical translation to PureFol reconstructs the source expression with the same free names. -/
theorem fromExprFormula_roundtrip {p : Expr} (hp : isFormula p)
    (hc : AllowedConstants p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop)
    {q : PureFol.Formula PureFolTranslation.language} (hq : fromExprFormula? p = some q) :
    AlphaBetaEta p ((PureFolEmbedding.toLambdaFormula q).reify Context.empty) := by
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hshape := FirstOrderShape.normalForm_isFirstOrder he hc hv
  have hr : fromNormalFormula? (fun _ => none) (normalize e) = some q := by
    simpa [fromExprFormula?, PureFolTranslation.normalizeExpr?, he] using hq
  have back := fromNormalFormula_roundtrip hshape (by simpa using hr)
  change AlphaBetaEta p ((PureFolEmbedding.formula (PureFolEmbedding.environment 0) q).reify _)
  rw [back]
  exact (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed he Context.empty)).trans
    ((normalize_sound e).reify Context.empty)

end Lisa.LambdaFol.PureFolTranslation

/-! Embed a first-order proof into Ordered, recovering the original concluding
formulas up to alpha-beta-eta equivalence. The public WithoutInstantiation theorem subsequently
passes this derivation through LambdaFol and eliminates instantiation. -/
namespace Lisa.LambdaFol.OrderedAlphaBetaEta

abbrev ProofTree := Ordered.ProofTree AlphaBetaEta
def Provable (Γ Δ : Finset Expr) : Prop := Nonempty (ProofTree Γ Δ)

open PureFolTranslation Orthologic.Derivation

/-- Embed a target derivation, then recover the exact original sequent by
alpha-beta-eta conversions and cuts. Free identifiers are preserved throughout. -/
theorem ofPureFol {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderCompatible p) (hbΔ : ∀ p ∈ Δ, FirstOrderCompatible p)
    (d : PureFol.Provable (canonicalFormulaSet Γ) (canonicalFormulaSet Δ)) :
    Provable Γ Δ := by
  have hn (p : Expr) (hp : p ∈ Γ ∪ Δ) :
      AlphaBetaEta p (PureFolEmbedding.toExprFormula (canonicalFormula p)) := by
    have hs := isFSet_union hΓ hΔ p hp
    have hb := (Finset.mem_union.mp hp).elim (hbΓ p) (hbΔ p)
    exact fromExprFormula_roundtrip hs hb.1 hb.2 (canonicalFormula_spec hs hb)
  have d' := PureFolEmbedding.provable_toOrdered d
  have d'' := OrderedDerivation.replaceLeft (PureFolEmbedding.formulaSet_sorted _) hΓ
    (PureFolEmbedding.formulaSet_sorted _) d' (fun q hq => by
      obtain ⟨q, hq', rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq'
      have hc := hn p (Finset.mem_union_left _ hp)
      have step := Orthologic.Derivation.convert (hΓ p hp) (hΓ p hp) (.refl _) hc
        (Ordered.ProofTree.hypothesis p (hΓ p hp))
      exact ⟨step.weakening (singleton_sorted (hΓ p hp))
        (singleton_sorted (PureFolEmbedding.toExprFormula_sort _)) hΓ
        (singleton_sorted (PureFolEmbedding.toExprFormula_sort _))
        (Finset.singleton_subset_iff.mpr hp) (by simp)⟩)
  apply OrderedDerivation.replaceRight hΓ (PureFolEmbedding.formulaSet_sorted _) hΔ d''
  intro q hq
  obtain ⟨q, hq', rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq'
  have hc := hn p (Finset.mem_union_right _ hp)
  have step := Orthologic.Derivation.convert (hΔ p hp) (hΔ p hp) hc (.refl _)
    (Ordered.ProofTree.hypothesis p (hΔ p hp))
  exact ⟨step.weakening (singleton_sorted (PureFolEmbedding.toExprFormula_sort _))
    (singleton_sorted (hΔ p hp)) (singleton_sorted (PureFolEmbedding.toExprFormula_sort _))
    hΔ (by simp) (Finset.singleton_subset_iff.mpr hp)⟩

end Lisa.LambdaFol.OrderedAlphaBetaEta
