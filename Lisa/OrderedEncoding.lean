import Lisa.Ordered
import Lisa.Sorting

open Lisa Expr

namespace Ordered

noncomputable section

private theorem sorted_fold (op : Expr → Expr → Expr)
    (hop : ∀ {p q}, isFormula p → isFormula q → isFormula (op p q))
    (l : List Expr) (a : Expr) (ha : isFormula a) (hl : isFSet l.toFinset) :
    isFormula (l.foldl op a) := by
  induction l generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    exact ih (op a b) (hop ha (hl b (by simp))) (fun p hp => hl p (by simp [hp]))

private theorem sorted_list_fold (op : Expr → Expr → Expr) (unit : Expr)
    (hop : ∀ {p q}, isFormula p → isFormula q → isFormula (op p q))
    (hu : isFormula unit) (l : List Expr) (hl : isFSet l.toFinset) :
    isFormula (foldFormulas op unit l) := by
  cases l with
  | nil => exact hu
  | cons a l =>
    exact sorted_fold op hop l a (hl a (by simp))
      (fun p hp => hl p (by simp [hp]))

theorem conjunction_sorted {Γ : Finset Expr} (hΓ : isFSet Γ) :
    isFormula (conjunction Γ) :=
  sorted_list_fold Expr.and top isFormula_and rfl Γ.toList (by simpa using hΓ)

theorem disjunction_sorted {Δ : Finset Expr} (hΔ : isFSet Δ) :
    isFormula (disjunction Δ) :=
  sorted_list_fold Expr.or bot isFormula_or rfl Δ.toList (by simpa using hΔ)

theorem sequentToFormula_sorted {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    isFormula (sequentToFormula Γ Δ) := by
  unfold sequentToFormula
  split
  · exact disjunction_sorted hΔ
  · exact isFormula_imp (conjunction_sorted hΓ) (disjunction_sorted hΔ)

private def packAnd {r : ExprRel} (l : List Expr) (a : Expr) {Δ : Finset Expr}
    (ha : isFormula a) (hl : isFSet l.toFinset) (hΔ : isFSet Δ)
    (pf : ProofTree r (insert a l.toFinset) Δ) :
    ProofTree r {l.foldl Expr.and a} Δ := by
  induction l generalizing a with
  | nil => simpa using pf
  | cons b bs ih =>
    have hb := hl b (by simp)
    have hbs : isFSet bs.toFinset := fun p hp => hl p (by simp [hp])
    exact ih (and a b) (isFormula_and ha hb) hbs
      (.leftAnd a b hbs hΔ ha hb (by simpa using pf))

private def packOr {r : ExprRel} (l : List Expr) (a : Expr) {Γ : Finset Expr}
    (ha : isFormula a) (hl : isFSet l.toFinset) (hΓ : isFSet Γ)
    (pf : ProofTree r Γ (insert a l.toFinset)) :
    ProofTree r Γ {l.foldl Expr.or a} := by
  induction l generalizing a with
  | nil => simpa using pf
  | cons b bs ih =>
    have hb := hl b (by simp)
    have hbs : isFSet bs.toFinset := fun p hp => hl p (by simp [hp])
    exact ih (or a b) (isFormula_or ha hb) hbs
      (.rightOr a b hΓ hbs ha hb (by simpa using pf))

private def proveAnd {r : ExprRel} (l : List Expr) (a : Expr) {Γ : Finset Expr}
    (ha : isFormula a) (hl : isFSet l.toFinset) (hΓ : isFSet Γ)
    (pa : ProofTree r Γ {a}) (ps : ∀ p ∈ l, ProofTree r Γ {p}) :
    ProofTree r Γ {l.foldl Expr.and a} := by
  induction l generalizing a with
  | nil => exact pa
  | cons b bs ih =>
    have hb := hl b (by simp)
    have pab : ProofTree r Γ {and a b} := by
      simpa using (ProofTree.rightAnd (Δ := ∅) (Ξ := ∅) a b hΓ (by simp [isFSet]) hΓ
        (by simp [isFSet]) ha hb pa (ps b (by simp)))
    exact ih (and a b) (isFormula_and ha hb) (fun p hp => hl p (by simp [hp]))
      pab (fun p hp => ps p (by simp [hp]))

private def useOr {r : ExprRel} (l : List Expr) (a : Expr) {Δ : Finset Expr}
    (ha : isFormula a) (hl : isFSet l.toFinset) (hΔ : isFSet Δ)
    (pa : ProofTree r {a} Δ) (ps : ∀ p ∈ l, ProofTree r {p} Δ) :
    ProofTree r {l.foldl Expr.or a} Δ := by
  induction l generalizing a with
  | nil => exact pa
  | cons b bs ih =>
    have hb := hl b (by simp)
    have pab : ProofTree r {or a b} Δ := by
      simpa using (ProofTree.leftOr (Γ := ∅) (Ω := ∅) a b (by simp [isFSet]) hΔ
        (by simp [isFSet]) hΔ ha hb pa (ps b (by simp)))
    exact ih (or a b) (isFormula_or ha hb) (fun p hp => hl p (by simp [hp]))
      pab (fun p hp => ps p (by simp [hp]))

private def proveConjunction {r : ExprRel} {Γ : Finset Expr} (hΓ : isFSet Γ) :
    ProofTree r Γ {conjunction Γ} := by
  have memProof : ∀ p ∈ Γ, ProofTree r Γ {p} := fun p hp =>
    .weakening (by simpa [isFSet] using hΓ p hp) (by simpa [isFSet] using hΓ p hp)
      hΓ (by simpa [isFSet] using hΓ p hp) (.hypothesis p (hΓ p hp))
      (by simpa using hp) (by rfl)
  cases he : Γ.toList with
  | nil =>
    have h : Γ = ∅ := by simpa using congrArg List.toFinset he
    subst Γ
    simpa [conjunction, foldFormulas] using (ProofTree.rightTrue (leq := r))
  | cons a l =>
    have hs : insert a l.toFinset = Γ := by simpa using (congrArg List.toFinset he).symm
    have ha : a ∈ Γ := by rw [← hs]; simp
    have hl : ∀ p ∈ l, p ∈ Γ := by intro p hp; rw [← hs]; simp [hp]
    simpa [conjunction, he, foldFormulas] using
      proveAnd l a (hΓ a ha) (fun p hp => hΓ p (hl p (by simpa using hp))) hΓ
        (memProof a ha) (fun p hp => memProof p (hl p hp))

private def useDisjunction {r : ExprRel} {Δ : Finset Expr} (hΔ : isFSet Δ) :
    ProofTree r {disjunction Δ} Δ := by
  have memProof : ∀ p ∈ Δ, ProofTree r {p} Δ := fun p hp =>
    .weakening (by simpa [isFSet] using hΔ p hp) (by simpa [isFSet] using hΔ p hp)
      (by simpa [isFSet] using hΔ p hp) hΔ (.hypothesis p (hΔ p hp))
      (by rfl) (by simpa using hp)
  cases he : Δ.toList with
  | nil =>
    have h : Δ = ∅ := by simpa using congrArg List.toFinset he
    subst Δ
    simpa [disjunction, foldFormulas] using (ProofTree.leftFalse (leq := r))
  | cons a l =>
    have hs : insert a l.toFinset = Δ := by simpa using (congrArg List.toFinset he).symm
    have ha : a ∈ Δ := by rw [← hs]; simp
    have hl : ∀ p ∈ l, p ∈ Δ := by intro p hp; rw [← hs]; simp [hp]
    simpa [disjunction, he, foldFormulas] using
      useOr l a (hΔ a ha) (fun p hp => hΔ p (hl p (by simpa using hp))) hΔ
        (memProof a ha) (fun p hp => memProof p (hl p hp))

/-- Pack a sequent into its formula using only logical rules and structural weakening. -/
def packSequent {r : ExprRel} {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (pf : ProofTree r Γ Δ) : ProofTree r ∅ {sequentToFormula Γ Δ} := by
  have right : ProofTree r Γ {disjunction Δ} := by
    cases he : Δ.toList with
    | nil =>
      have h : Δ = ∅ := by simpa using congrArg List.toFinset he
      subst Δ
      exact .weakening hΓ (by simp [isFSet]) hΓ (by simp [isFSet, disjunction, foldFormulas, isFormula, hasSort, Expr.bot])
        pf (by rfl) (Finset.empty_subset _)
    | cons a l =>
      have hs : insert a l.toFinset = Δ := by simpa using (congrArg List.toFinset he).symm
      have hl : isFSet (insert a l.toFinset) := hs ▸ hΔ
      simpa [disjunction, he, foldFormulas] using
        packOr l a (hl a (by simp)) (fun p hp => hl p (by simp [hp])) hΓ (hs ▸ pf)
  by_cases h : Γ = ∅
  · simpa [sequentToFormula, h] using right
  · have left : ProofTree r {conjunction Γ} {disjunction Δ} := by
      cases he : Γ.toList with
      | nil => exact False.elim (h (by simpa using congrArg List.toFinset he))
      | cons a l =>
        have hs : insert a l.toFinset = Γ := by simpa using (congrArg List.toFinset he).symm
        have hl : isFSet (insert a l.toFinset) := hs ▸ hΓ
        simpa [conjunction, he, foldFormulas] using
          packAnd l a (hl a (by simp)) (fun p hp => hl p (by simp [hp]))
            (by simpa [isFSet] using disjunction_sorted hΔ) (hs ▸ right)
    simpa [sequentToFormula, h] using
      (ProofTree.rightImp (Γ := ∅) (Δ := ∅) (conjunction Γ) (disjunction Δ) (by simp [isFSet])
        (by simp [isFSet]) (conjunction_sorted hΓ) (disjunction_sorted hΔ) left)

/-- The encoded formula entails its original sequent, without assumptions on the relation. -/
def useSequentFormula {r : ExprRel} {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    ProofTree r (insert (sequentToFormula Γ Δ) Γ) Δ := by
  by_cases h : Γ = ∅
  · simpa [sequentToFormula, h] using (useDisjunction (r := r) hΔ)
  · simpa [sequentToFormula, h] using
      (ProofTree.leftImp (Δ := ∅) (Ω := ∅) (conjunction Γ) (disjunction Δ) hΓ (by simp [isFSet])
        (by simp [isFSet]) hΔ (conjunction_sorted hΓ) (disjunction_sorted hΔ)
        (proveConjunction hΓ) (useDisjunction hΔ))

end
end Ordered
