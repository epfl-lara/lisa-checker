import Lisa.SCLambdaToPure.AToPure.Reverse.Roundtrip
import Lisa.SCLambdaToPure.AToPure.Reverse.Derivation
import Lisa.SCLambdaToPure.AToPure.Boundary

/-! Every expression at the first-order epsilon boundary has a first-order
representation, with an alpha-beta-eta roundtrip. This module concerns
expressions; `OrderedReduction.ofPure` below transports complete derivations. -/
namespace Lisa.SCLambdaToPure.Readback
open Lambda
open FirstOrderShape (ConstantsInLanguage)

/-- Canonical readback reconstructs the source expression with the same free names. -/
theorem readFormula_roundtrip {p : Expr} (hp : isFormula p)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop)
    {q : Pure.Formula Readback.language} (hq : readFormula p = some q) :
    AlphaBetaEta p ((PureEmbedding.ofFormula q).reify Context.empty) := by
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hshape := FirstOrderShape.normalize_named_formula he
    (FirstOrderShape.inLanguage_of_interpretNamed he hc hv)
  have hr : formula (fun _ => none) (normalize e) = some q := by
    simpa [readFormula, Readback.normalized, he] using hq
  have back := formula_roundtrip hshape (PureEmbedding.environment 0)
    (fun _ => none) (by simp) (by intros; rfl) hr
  change AlphaBetaEta p ((PureEmbedding.formula (PureEmbedding.environment 0) q).reify _)
  rw [back]
  exact (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed he Context.empty)).trans
    ((normalize_sound e).reify Context.empty)

/-- The expression representation result, with exact canonical readback.
Free individual identifiers are preserved directly. -/
theorem formula_representation {p : Expr} (hp : isFormula p)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    ∃ q : Pure.Formula Readback.language,
      readFormula p = some q ∧
        AlphaBetaEta p ((PureEmbedding.ofFormula q).reify Context.empty) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (readFormula_isSome hp hc hv)
  exact ⟨q, hq, readFormula_roundtrip hp hc hv hq⟩

/-- Individual terms have the same representation property, including epsilon. -/
theorem term_representation {p : Expr} (hp : isTerm p)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    ∃ t : Pure.Term Readback.language,
      readTerm p = some t ∧
        AlphaBetaEta p ((PureEmbedding.ofTerm t).reify Context.empty) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (readTerm_isSome hp hc hv)
  refine ⟨t, ht, ?_⟩
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hshape := FirstOrderShape.normalize_individual
    (FirstOrderShape.inLanguage_of_interpretNamed he hc hv) (subst_of_interpretNamed he)
  have hr : term (fun _ => none) (normalize e) = some t := by
    simpa [readTerm, Readback.normalized, he] using ht
  have back := term_roundtrip hshape (PureEmbedding.environment 0)
    (fun _ => none) (by simp) (by intros; rfl) hr
  change AlphaBetaEta p ((PureEmbedding.term (PureEmbedding.environment 0) t).reify _)
  rw [back]
  exact (AlphaBetaEta.alpha (alpha_reify_of_interpretNamed he Context.empty)).trans
    ((normalize_sound e).reify Context.empty)

/-- The representation is provably equivalent in the actual source system.
The complete derivation translation is `OrderedReduction.ofPure` below.
-/
theorem formula_provable_equivalence {p : Expr} (hp : isFormula p)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    ∃ q : Pure.Formula Readback.language,
      readFormula p = some q ∧
        Nonempty (Ordered.AlphaBetaEtaProof ∅
          {Expr.iff p ((PureEmbedding.ofFormula q).reify Context.empty)}) := by
  obtain ⟨q, hq, h⟩ := formula_representation hp hc hv
  refine ⟨q, hq, ?_⟩
  have he := (PureEmbedding.ofFormula q).reify_sort Context.empty
  exact ⟨Orthologic.Derivation.iff_intro hp he
    (Orthologic.Derivation.convert hp hp (.refl _) h (.hypothesis p hp))
    (Orthologic.Derivation.convert hp hp h (.refl _) (.hypothesis p hp))⟩

end Lisa.SCLambdaToPure.Readback

/-! Embed a first-order proof into Ordered, recovering the original concluding
formulas up to alpha-beta-eta equivalence. The public A theorem subsequently
passes this derivation through B and eliminates instantiation.
This is an existing reverse-proof construction, not another proof system. -/
namespace Lisa.SCLambdaToPure.OrderedReduction

abbrev ProofTree := Ordered.ProofTree AlphaBetaEta
def Provable (Γ Δ : Finset Expr) : Prop := Nonempty (ProofTree Γ Δ)

open Readback Orthologic.Derivation

/-- Embed a target derivation, then recover the exact original sequent by
alpha-beta-eta conversions and cuts. Free identifiers are preserved throughout. -/
theorem ofPure {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (hbΓ : ∀ p ∈ Γ, FirstOrderBoundary p) (hbΔ : ∀ p ∈ Δ, FirstOrderBoundary p)
    (d : Pure.Provable (canonicalContext Γ) (canonicalContext Δ)) :
    Provable Γ Δ := by
  have hn (p : Expr) (hp : p ∈ Γ ∪ Δ) :
      AlphaBetaEta p (PureEmbedding.reifyFormula (canonical p)) := by
    have hs := isFSet_union hΓ hΔ p hp
    have hb := (Finset.mem_union.mp hp).elim (hbΓ p) (hbΔ p)
    exact readFormula_roundtrip hs hb.1 hb.2 (canonical_spec hs hb)
  have d' := PureEmbedding.provable_toOrdered d
  have d'' := OrderedDerivation.replaceLeft (PureEmbedding.context_sorted _) hΓ
    (PureEmbedding.context_sorted _) d' (fun q hq => by
      obtain ⟨q, hq', rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq'
      have hc := hn p (Finset.mem_union_left _ hp)
      have step := Orthologic.Derivation.convert (hΓ p hp) (hΓ p hp) (.refl _) hc
        (Ordered.ProofTree.hypothesis p (hΓ p hp))
      exact ⟨step.weakening (singleton_sorted (hΓ p hp))
        (singleton_sorted (PureEmbedding.reifyFormula_sort _)) hΓ
        (singleton_sorted (PureEmbedding.reifyFormula_sort _))
        (Finset.singleton_subset_iff.mpr hp) (by simp)⟩)
  apply OrderedDerivation.replaceRight hΓ (PureEmbedding.context_sorted _) hΔ d''
  intro q hq
  obtain ⟨q, hq', rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq'
  have hc := hn p (Finset.mem_union_right _ hp)
  have step := Orthologic.Derivation.convert (hΔ p hp) (hΔ p hp) hc (.refl _)
    (Ordered.ProofTree.hypothesis p (hΔ p hp))
  exact ⟨step.weakening (singleton_sorted (PureEmbedding.reifyFormula_sort _))
    (singleton_sorted (hΔ p hp)) (singleton_sorted (PureEmbedding.reifyFormula_sort _))
    hΔ (by simp) (Finset.singleton_subset_iff.mpr hp)⟩


end Lisa.SCLambdaToPure.OrderedReduction
