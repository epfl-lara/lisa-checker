import Lisa.Orthologic.CachedSoundness
import Lisa.OrderedComparison
import Lisa.OrderedWeakened

/-! The relation used in checker certificates is justified by actual Ordered
αβη proofs. The executable OL algorithm is a sound, incomplete test for it;
there is deliberately no `DecidableRel` instance for this relation. -/

namespace Imported.Checker
open Lisa Expr Orthologic

def ProofRelation (p q : Expr) : Prop :=
  p.sort = q.sort ∧ ∀ s, p.hasSort s →
    match s with
    | .prop => Nonempty (Ordered.AlphaBetaEtaProof {p} {q})
    | s => ContextEq s p q

namespace ProofRelation

theorem of_context (hp : p.hasSort s) (hq : q.hasSort s) (h : ContextEq s p q) :
    isSame ProofRelation p q := by
  have one {p q : Expr} (hp : p.hasSort s) (hq : q.hasSort s) (h : ContextEq s p q) :
      ProofRelation p q := by
    refine ⟨hp.trans hq.symm, ?_⟩
    intro t ht
    have : t = s := Option.some.inj (ht.symm.trans hp)
    subst t
    cases s with
    | prop => exact (h.formula hp hq).1
    | ind => exact h
    | arrow => exact h
  exact ⟨one hp hq h, one hq hp h.symm⟩

theorem context (hp : p.hasSort s) (h : isSame ProofRelation p q) : ContextEq s p q := by
  have hq : q.hasSort s := h.1.1.symm.trans hp
  cases s with
  | prop => exact ContextEq.of_formula hp hq (h.1.2 _ hp) (h.2.2 _ hq)
  | ind => exact h.1.2 _ hp
  | arrow => exact h.1.2 _ hp

instance : IsPreorder Expr ProofRelation where
  refl p := ⟨rfl, fun s hp => by
    cases s with
    | prop => exact ⟨.hypothesis p hp⟩
    | ind => exact ContextEq.refl hp
    | arrow => exact ContextEq.refl hp⟩
  trans p q r h k := by
    refine ⟨h.1.trans k.1, fun s hp => ?_⟩
    have hq : q.hasSort s := h.1.symm.trans hp
    have hr : r.hasSort s := k.1.symm.trans hq
    cases s with
    | prop => exact ⟨Derivation.trans hp hq hr (Classical.choice (h.2 _ hp))
        (Classical.choice (k.2 _ hq))⟩
    | ind => exact ContextEq.trans hp hq hr (h.2 _ hp) (k.2 _ hq)
    | arrow => exact ContextEq.trans hp hq hr (h.2 _ hp) (k.2 _ hq)

theorem formula (hp : isFormula p) (hq : isFormula q)
    (h : Nonempty (Ordered.AlphaBetaEtaProof {p} {q})) : ProofRelation p q := by
  refine ⟨hp.trans hq.symm, fun s hs => ?_⟩
  have : s = prop := Option.some.inj (hs.symm.trans hp)
  subst s
  exact h

private theorem binary_context (c : SConst) (hc : (Expr.const c).hasSort (s >> t >> u))
    (hp : p.hasSort s) (hp' : p'.hasSort s) (hq : q.hasSort t) (hq' : q'.hasSort t)
    (h : ContextEq s p p') (k : ContextEq t q q') :
    ContextEq u (.app (.app (.const c) p) q) (.app (.app (.const c) p') q') :=
  ContextEq.app (ContextEq.app_sort hc hp) (ContextEq.app_sort hc hp') hq hq'
    (ContextEq.app hc hc hp hp' (ContextEq.refl hc) h) k

instance : RelationCongruence ProofRelation where
  eq_congr := by
    intro s s' t t' hs hs' ht ht' h k
    exact of_context (isFormula_eq hs ht) (isFormula_eq hs' ht')
      (binary_context _ rfl hs hs' ht ht' (context hs h) (context ht k))
  imp_congr := by
    intro p p' q q' h k
    have sortEq : (imp p q).sort = (imp p' q').sort := by
      simp only [Expr.imp, Expr.sort, h.1.1, k.1.1]
    by_cases hp : isFormula p
    · by_cases hq : isFormula q
      · have hp' : isFormula p' := h.1.1.symm.trans hp
        have hq' : isFormula q' := k.1.1.symm.trans hq
        exact of_context (isFormula_imp hp hq) (isFormula_imp hp' hq')
          (binary_context _ rfl hp hp' hq hq' (context hp h) (context hq k))
      · have hn : (imp p q).sort = none := by
          cases he : q.sort with
          | none => simp [Expr.imp, show p.sort = some prop from hp, he]
          | some s =>
            have hs : s ≠ prop := by intro h; apply hq; simp [hasSort, he, h]
            simp [Expr.imp, show p.sort = some prop from hp, he, hs]
        exact ⟨⟨sortEq, fun s hs => by simp [hasSort, hn] at hs⟩,
          ⟨sortEq.symm, fun s hs => by simp [hasSort, ← sortEq, hn] at hs⟩⟩
    · have hn : (imp p q).sort = none := by
        cases he : p.sort with
        | none => simp [Expr.imp, he]
        | some s =>
          have hs : s ≠ prop := by intro h; apply hp; simp [hasSort, he, h]
          simp [Expr.imp, he, hs]
      exact ⟨⟨sortEq, fun s hs => by simp [hasSort, hn] at hs⟩,
        ⟨sortEq.symm, fun s hs => by simp [hasSort, ← sortEq, hn] at hs⟩⟩

noncomputable def admissible : Ordered.Admissible ProofRelation AlphaBetaEta :=
  fun _ _ hp _ h => Classical.choice (h.2 prop hp)

theorem of_alphaBetaEta : Subrelation AlphaBetaEta ProofRelation := by
  intro p q h
  refine ⟨h.preserves_sort, fun s hp => ?_⟩
  have hq : q.hasSort s := h.preserves_sort.symm.trans hp
  exact (of_context hp hq (ContextEq.of_conversion hp h)).1.2 s hp

theorem of_same (h : Orthologic.Cached.isSame p q = some true) : isSame ProofRelation p q := by
  obtain ⟨s, hp, hq, he⟩ := Orthologic.Cached.isSame_sound h
  exact of_context hp hq he

theorem of_implying (h : Orthologic.Cached.isImplying p q = some true) : ProofRelation p q := by
  have he : Orthologic.isImplying p q = some true := by
    simpa only [Orthologic.Cached.isImplying_eq] using h
  obtain ⟨_, _, hp, hq, _⟩ := Orthologic.isImplying_true.mp he
  exact formula (Orthologic.prepare_hasSort hp) (Orthologic.prepare_hasSort hq)
    (Orthologic.isImplying_sound he)

end ProofRelation
end Imported.Checker
