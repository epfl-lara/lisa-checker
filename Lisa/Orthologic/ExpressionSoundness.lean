import Lisa.Orthologic.Expression
import Lisa.Orthologic.LoweringSoundness
import Lisa.Orthologic.NormalizationSoundness

/-! Public guarantees for the named LambdaFOL pipeline. Accepted comparisons
give proofs in Ordered instantiated with alpha-beta-eta, including contextual
replacement at function sorts. No completeness claim is made. -/

namespace Lisa.Orthologic
open Derivation

theorem prepare_sort (p : Expr) : (prepare p).map Sigma.fst = p.sort := by
  rw [← Lambda.interpretNamed_sort p Lambda.Names.free]
  cases h : Lambda.interpretNamed p Lambda.Names.free with
  | none => simp [prepare, h]
  | some e => cases e; simp [prepare, h]

theorem prepare_hasSort (h : prepare p = some ⟨s, e⟩) : p.hasSort s := by
  simpa [h] using (prepare_sort p).symm

theorem prepare_none (p : Expr) : prepare p = none ↔ p.sort = none := by
  rw [prepare, Option.map_eq_none_iff, Lambda.interpretNamed_none]

theorem normalize_none (p : Expr) : normalize p = none ↔ p.sort = none := by
  rw [normalize, Option.map_eq_none_iff, prepare_none]

theorem normalize_sort (h : normalize p = some q) : p.sort = q.sort := by
  cases he : prepare p with
  | none => simp [normalize, he] at h
  | some e =>
      obtain ⟨s, e⟩ := e
      simp only [normalize, he, Option.map_some, Option.some.injEq] at h
      subst q
      exact (prepare_hasSort he).trans (e.reify_sort _).symm

/-- Alpha-renaming has no effect on the internal normalized expression. -/
theorem prepare_alpha (h : AlphaEq p q) : prepare p = prepare q := by
  unfold prepare
  rw [Lambda.interpretNamed_alpha h]

/-- The OL stage receives the same input for alpha-beta-eta equivalent terms. -/
theorem prepare_alphaBetaEta (hp : p.hasSort s) (h : AlphaBetaEta p q) :
    prepare p = prepare q := by
  obtain ⟨e, he⟩ := Lambda.interpretNamed_sorted hp Lambda.Names.free
  obtain ⟨f, hf⟩ := Lambda.interpretNamed_sorted (h.preserves_sort.symm.trans hp) Lambda.Names.free
  have ht := Lambda.interpretNamed_alphaBetaEta h Lambda.Names.free
  rw [he, hf] at ht
  cases ht with
  | some ht => simp [prepare, he, hf, Lambda.normalize_eq_of_equiv ht]

theorem normalize_alphaBetaEta (hp : p.hasSort s) (h : AlphaBetaEta p q) :
    normalize p = normalize q := by
  unfold normalize
  rw [prepare_alphaBetaEta hp h]

/-- The complete pipeline preserves contextual equivalence at the input sort. -/
theorem prepare_sound (h : prepare p = some ⟨s, e⟩) :
    ContextEq s p (e.reify Lambda.Context.empty) := by
  cases he : Lambda.interpretNamed p Lambda.Names.free with
  | none => simp [prepare, he] at h
  | some t =>
      obtain ⟨t, b⟩ := t
      simp only [prepare, he, Option.map_some, Option.some.injEq] at h
      cases h
      have hp := Lambda.hasSort_of_interpretNamed he
      have hc := (AlphaBetaEta.alpha (Lambda.alpha_reify_of_interpretNamed he Lambda.Context.empty)).trans
        ((Lambda.normalize_sound b).reify Lambda.Context.empty)
      have hb := Lambda.Term.reify_sort (Lambda.normalize b) Lambda.Context.empty
      have hl := SimpleExpr.reify_sort (SimpleExpr.ofTerm (Lambda.normalize b)) Lambda.Context.empty
      have hn := SimpleExpr.reify_sort (computeNormalForm (SimpleExpr.ofTerm (Lambda.normalize b))) Lambda.Context.empty
      exact ContextEq.trans hp hb hn (ContextEq.of_conversion hp hc)
        (ContextEq.trans hb hl hn (SimpleExpr.ofTerm_sound _ _).symm
          ((computeNormalForm_sound _).symm Lambda.Context.empty))

theorem normalize_sound (hp : p.hasSort s) (h : normalize p = some q) :
    ContextEq s p q := by
  cases he : prepare p with
  | none => simp [normalize, he] at h
  | some e =>
      obtain ⟨t, e⟩ := e
      have hs : t = s := Option.some.inj ((prepare_hasSort he).symm.trans hp)
      subst t
      simp only [normalize, he, Option.map_some, Option.some.injEq] at h
      subst q
      exact prepare_sound he

/-- In particular, formula normalization is justified in both directions. -/
theorem normalize_formula_sound (hp : isFormula p) (h : normalize p = some q) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) ∧
      Nonempty (Ordered.AlphaBetaEtaProof {q} {p}) :=
  ContextEq.formula hp ((normalize_sort h).symm.trans hp) (normalize_sound hp h)

theorem isSame_true : isSame p q = some true ↔
    ∃ s, ∃ e f : SimpleExpr s,
      prepare p = some ⟨s, e⟩ ∧ prepare q = some ⟨s, f⟩ ∧ latticesEQ e f = true := by
  constructor
  · intro h
    cases hp : prepare p with
    | none => simp [isSame, hp] at h
    | some e =>
      obtain ⟨s, e⟩ := e
      cases hq : prepare q with
      | none => simp [isSame, hp, hq] at h
      | some f =>
        obtain ⟨t, f⟩ := f
        by_cases hs : t = s
        · subst t
          exact ⟨s, e, f, rfl, rfl, by simpa [isSame, hp, hq] using h⟩
        · simp [isSame, hp, hq, hs] at h
  · rintro ⟨s, e, f, hp, hq, h⟩
    simp [isSame, hp, hq, h]

theorem isSame_none (p q : Expr) : isSame p q = none ↔ p.sort = none ∨ q.sort = none := by
  rw [← prepare_none p, ← prepare_none q]
  cases hp : prepare p with
  | none => simp [isSame, hp]
  | some e =>
    obtain ⟨s, e⟩ := e
    cases hq : prepare q with
    | none => simp [isSame, hp, hq]
    | some f =>
      obtain ⟨t, f⟩ := f
      by_cases hs : t = s <;> simp [isSame, hp, hq, hs]

theorem isSame_refl (hp : p.hasSort s) : isSame p p = some true := by
  cases he : prepare p with
  | none => have hn := (prepare_none p).mp he; simp [Expr.hasSort, hn] at hp
  | some e =>
      obtain ⟨t, e⟩ := e
      have hr : latticesEQ e e = true := by unfold latticesEQ; simp
      simp [isSame, he, hr]

/-- All well-sorted alpha-beta-eta equivalences are recognized, independently
of which additional equivalences the incomplete OL stage can establish. -/
theorem isSame_of_alphaBetaEta (hp : p.hasSort s) (h : AlphaBetaEta p q) :
    isSame p q = some true := by
  simpa only [isSame, ← prepare_alphaBetaEta hp h] using isSame_refl hp

/-- Accepted equivalence is usable in any well-sorted formula context. -/
theorem isSame_sound (h : isSame p q = some true) :
    ∃ s, p.hasSort s ∧ q.hasSort s ∧ ContextEq s p q := by
  obtain ⟨s, e, f, hp, hq, h⟩ := isSame_true.mp h
  have hs := prepare_hasSort hp
  have ht := prepare_hasSort hq
  exact ⟨s, hs, ht, ContextEq.trans hs (e.reify_sort _) ht (prepare_sound hp)
    (ContextEq.trans (e.reify_sort _) (f.reify_sort _) ht
      (latticesEQ_sound e f h Lambda.Context.empty) (prepare_sound hq).symm)⟩

theorem isSame_formula_sound (hp : isFormula p) (h : isSame p q = some true) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) ∧
      Nonempty (Ordered.AlphaBetaEtaProof {q} {p}) := by
  obtain ⟨s, hs, ht, h⟩ := isSame_sound h
  have : s = prop := Option.some.inj (hs.symm.trans hp)
  subst s
  exact ContextEq.formula hs ht h

theorem isImplying_true : isImplying p q = some true ↔
    ∃ e f : SimpleExpr prop,
      prepare p = some ⟨prop, e⟩ ∧ prepare q = some ⟨prop, f⟩ ∧ latticesLEQ e f = true := by
  constructor
  · intro h
    cases hp : prepare p with
    | none => simp [isImplying, hp] at h
    | some e =>
      obtain ⟨s, e⟩ := e
      cases s <;> simp [isImplying, hp] at h
      cases hq : prepare q with
      | none => simp [hq] at h
      | some f =>
        obtain ⟨t, f⟩ := f
        cases t <;> simp [hq] at h
        exact ⟨e, f, rfl, rfl, h⟩
  · rintro ⟨e, f, hp, hq, h⟩
    simp [isImplying, hp, hq, h]

theorem isImplying_none (p q : Expr) :
    isImplying p q = none ↔ p.sort ≠ some prop ∨ q.sort ≠ some prop := by
  rw [← prepare_sort p, ← prepare_sort q]
  cases hp : prepare p with
  | none => simp [isImplying, hp]
  | some e =>
    obtain ⟨s, e⟩ := e
    cases s <;> simp [isImplying, hp]
    cases hq : prepare q with
    | none => simp
    | some f => obtain ⟨t, f⟩ := f; cases t <;> simp

/-- Successful implication comparison gives an actual Ordered proof. -/
theorem isImplying_sound (h : isImplying p q = some true) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) := by
  obtain ⟨e, f, hp, hq, h⟩ := isImplying_true.mp h
  have hs := prepare_hasSort hp
  have ht := prepare_hasSort hq
  obtain ⟨d⟩ := (ContextEq.formula hs (e.reify_sort _) (prepare_sound hp)).1
  obtain ⟨c⟩ := latticesLEQ_sound h Lambda.Context.empty
  obtain ⟨b⟩ := (ContextEq.formula ht (f.reify_sort _) (prepare_sound hq)).2
  exact ⟨Derivation.trans hs (e.reify_sort _) ht d
    (Derivation.trans (e.reify_sort _) (f.reify_sort _) ht c b)⟩

end Lisa.Orthologic
