import Lisa.Checker.ProofRelation

/-! Wire lists and abstract finite sets encode provably equivalent sequents.
The bridge uses logical proof steps, independently of OL comparison success. -/
namespace Imported.Checker
open Lisa Expr Orthologic
open Derivation

def listSequentToFormula (pre post : List Expr) : Expr :=
  if pre.isEmpty then foldFormulas or bot post
  else imp (foldFormulas and top pre) (foldFormulas or bot post)

private theorem sorted_fold (op : Expr → Expr → Expr) (unit : Expr)
    (hop : ∀ {p q}, isFormula p → isFormula q → isFormula (op p q))
    (hu : isFormula unit) (ps : List Expr) (hs : ∀ p ∈ ps, isFormula p) :
    isFormula (foldFormulas op unit ps) := by
  cases ps with
  | nil => exact hu
  | cons p ps =>
    simp only [foldFormulas]
    have hp := hs p (by simp)
    have hps : ∀ q ∈ ps, isFormula q := fun q hq => hs q (by simp [hq])
    clear hs
    induction ps generalizing p with
    | nil => exact hp
    | cons q qs ih =>
      exact ih (op p q) (hop hp (hps q (by simp)))
        (by intro r hr; exact hps r (by simp [hr]))

private theorem and_spec (ps : List Expr) (hs : ∀ p ∈ ps, isFormula p)
    (hr : isFormula r) :
    ProofRelation r (foldFormulas and top ps) ↔ ∀ p ∈ ps, ProofRelation r p := by
  have hf := sorted_fold and top isFormula_and rfl ps hs
  cases ps with
  | nil => simp only [foldFormulas, List.not_mem_nil, false_implies, implies_true, iff_true]
           exact ProofRelation.formula hr rfl ⟨le_top hr⟩
  | cons p ps =>
    have hp := hs p (by simp)
    have hps : ∀ q ∈ ps, isFormula q := fun q hq => hs q (by simp [hq])
    constructor
    · intro h q hq
      obtain ⟨head, tail⟩ := fold_and_le hp hps
      have d := h.2 prop hr
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ProofRelation.formula hr hp ⟨trans hr hf hp (Classical.choice d) (Classical.choice head)⟩
      · exact ProofRelation.formula hr (hps q hq)
          ⟨trans hr hf (hps q hq) (Classical.choice d) (Classical.choice (tail q hq))⟩
    · intro h
      exact ProofRelation.formula hr hf (le_fold_and hr hp hps
        ((h p (by simp)).2 prop hr) (fun q hq => (h q (by simp [hq])).2 prop hr))

private theorem or_binary (hp : isFormula p) (hq : isFormula q) (hr : isFormula r) :
    ProofRelation (or p q) r ↔ ProofRelation p r ∧ ProofRelation q r := by
  have hpq := isFormula_or hp hq
  constructor
  · intro h
    obtain ⟨d⟩ := h.2 prop hpq
    exact ⟨ProofRelation.formula hp hr ⟨trans hp hpq hr (or_left hp hq) d⟩,
      ProofRelation.formula hq hr ⟨trans hq hpq hr (or_right hp hq) d⟩⟩
  · rintro ⟨h, k⟩
    exact ProofRelation.formula hpq hr
      ⟨or_le hp hq hr (Classical.choice (h.2 prop hp)) (Classical.choice (k.2 prop hq))⟩

private theorem or_fold (ps : List Expr) (hs : ∀ p ∈ ps, isFormula p)
    (hp : isFormula p) (hr : isFormula r) :
    ProofRelation (ps.foldl or p) r ↔ ProofRelation p r ∧ ∀ q ∈ ps, ProofRelation q r := by
  induction ps generalizing p with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, ih (fun q hq => hs q (by simp [hq])) (isFormula_or hp (hs q (by simp))),
      or_binary hp (hs q (by simp)) hr]
    simp [and_assoc]

private theorem or_spec (ps : List Expr) (hs : ∀ p ∈ ps, isFormula p) (hr : isFormula r) :
    ProofRelation (foldFormulas or bot ps) r ↔ ∀ p ∈ ps, ProofRelation p r := by
  cases ps with
  | nil => simp only [foldFormulas, List.not_mem_nil, false_implies, implies_true, iff_true]
           exact ProofRelation.formula rfl hr ⟨bot_le hr⟩
  | cons p ps =>
      simpa [foldFormulas] using
        or_fold ps (fun q hq => hs q (by simp [hq])) (hs p (by simp)) hr

private theorem folds_same (ps : List Expr) (hs : isFSet ps.toFinset) :
    isSame ProofRelation (foldFormulas and top ps) (conjunction ps.toFinset) ∧
    isSame ProofRelation (foldFormulas or bot ps) (disjunction ps.toFinset) := by
  have hl : ∀ p ∈ ps, isFormula p := by simpa using hs
  have ht : ∀ p ∈ ps.toFinset.toList, isFormula p := by simpa using hs
  have ha := sorted_fold and top isFormula_and rfl ps hl
  have hb := sorted_fold or bot isFormula_or rfl ps hl
  have hc := Ordered.conjunction_sorted hs
  have hd := Ordered.disjunction_sorted hs
  constructor
  · constructor
    · apply (and_spec _ ht ha).mpr
      simpa using (and_spec _ hl ha).mp (OrderLaws.self_le _)
    · apply (and_spec _ hl hc).mpr
      simpa using (and_spec _ ht hc).mp (OrderLaws.self_le _)
  · constructor
    · apply (or_spec _ hl hd).mpr
      simpa using (or_spec _ ht hd).mp (OrderLaws.self_le _)
    · apply (or_spec _ ht hb).mpr
      simpa using (or_spec _ hl hb).mp (OrderLaws.self_le _)

theorem listSequent_same (pre post : List Expr) (hp : isFSet pre.toFinset)
    (hq : isFSet post.toFinset) :
    isSame ProofRelation (listSequentToFormula pre post)
      (sequentToFormula pre.toFinset post.toFinset) := by
  cases pre with
  | nil => simpa [listSequentToFormula, sequentToFormula] using (folds_same post hq).2
  | cons p ps =>
    simpa [listSequentToFormula, sequentToFormula] using
      RelationCongruence.imp_congr (leq := ProofRelation) (folds_same (p :: ps) hp).1
        (folds_same post hq).2

end Imported.Checker
