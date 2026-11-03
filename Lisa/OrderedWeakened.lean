import Lisa.Sorting
import Lisa.Ordered
import Lisa.Weakened
import Aesop

open Lisa
open Expr

noncomputable section

/-- Discharge canonical contexts using finite-set membership and reflexivity. -/
local macro "lisa_context" : tactic =>
  `(tactic| (simp_all only [setLeq, containedExcept, containedExceptEither,
    ordContains, isSame, OrderLaws.self_le,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    List.mem_cons, List.mem_singleton, List.not_mem_nil,
    and_true, true_and, true_or, or_true, false_or, or_false,
    forall_true_left, exists_eq_left, exists_eq_right] <;>
      (aesop (add safe apply OrderLaws.self_le)
        (config := { enableSimp := false }))))

@[simp] private theorem isSame_refl {leq : ExprRel} [Std.Refl leq] (α : Expr) :
    isSame leq α α := by
  exact ⟨OrderLaws.self_le α, OrderLaws.self_le α⟩

@[simp] private theorem ordContains_refl {leq : ExprRel} [Std.Refl leq] (α : Expr) (Γ : Finset Expr) :
    ordContains leq α (insert α Γ) := by
  exact ⟨α, by simp, isSame_refl α⟩

@[simp] private theorem setLeq_refl {leq : ExprRel} [Std.Refl leq] (Γ : Finset Expr) :
    setLeq leq Γ Γ := by
  intro φ hφ
  exact ⟨φ, hφ, isSame_refl φ⟩

private theorem setLeq_insert_of_same {leq : ExprRel} [Std.Refl leq]
    {Γ : Finset Expr} {α β : Expr} (h : isSame leq α β) :
    setLeq leq (insert α Γ) (insert β Γ) := by
  intro φ hφ
  rcases Finset.mem_insert.mp hφ with rfl | hφ
  · exact ⟨β, Finset.mem_insert_self _ _, h⟩
  · exact ⟨φ, Finset.mem_insert_of_mem hφ, isSame_refl φ⟩

private theorem setLeq_singleton_of_same {leq : ExprRel} {α β : Expr}
    (h : isSame leq α β) : setLeq leq {α} {β} := by
  intro φ hφ
  obtain rfl := Finset.mem_singleton.mp hφ
  exact ⟨β, Finset.mem_singleton_self _, h⟩

@[simp] private theorem sequentLeq_refl {leq : ExprRel} [Std.Refl leq] (Γ Δ : Finset Expr) :
    sequentLeq leq Γ Δ Γ Δ := by
  unfold sequentLeq
  exact OrderLaws.self_le _

private theorem setLeq_empty {leq : ExprRel} (Γ : Finset Expr) :
    setLeq leq ∅ Γ := by
  intro φ hφ
  simp at hφ

private theorem setLeq_to_insert_of_containedExcept {leq : ExprRel}
    {Γ Ω : Finset Expr} {α : Expr} (h : containedExcept leq Γ Ω α) :
    setLeq leq Γ (insert α Ω) := by
  intro φ hφ
  rcases h φ hφ with ⟨ψ, hψ, heq⟩ | heq
  · exact ⟨ψ, Finset.mem_insert_of_mem hψ, heq⟩
  · exact ⟨α, Finset.mem_insert_self _ _, heq⟩

private theorem setLeq_to_insert₂_of_containedExceptEither {leq : ExprRel}
    {Γ Ω : Finset Expr} {α β : Expr} (h : containedExceptEither leq Γ Ω α β) :
    setLeq leq Γ (insert α (insert β Ω)) := by
  intro φ hφ
  rcases h φ hφ with hΩ | hα | hβ
  · obtain ⟨ψ, hψ, heq⟩ := hΩ
    exact ⟨ψ, by simp [hψ], heq⟩
  · exact ⟨α, by simp, hα⟩
  · exact ⟨β, by simp, hβ⟩

private theorem setLeq_insert_of_ordContains {leq : ExprRel} [Std.Refl leq]
    {Γ : Finset Expr} {α : Expr}
    (hα : ordContains leq α Γ) :
    setLeq leq (insert α Γ) Γ := by
  intro φ hφ
  simp only [Finset.mem_insert] at hφ
  rcases hφ with rfl | hφ
  · exact hα
  · exact ⟨φ, hφ, isSame_refl φ⟩

private theorem setLeq_singleton_of_ordContains {leq : ExprRel}
    {Γ : Finset Expr} {α : Expr}
    (hα : ordContains leq α Γ) :
    setLeq leq {α} Γ := by
  intro φ hφ
  simp only [Finset.mem_singleton] at hφ
  subst φ
  exact hα

private theorem setLeq_union_self {leq : ExprRel} [Std.Refl leq]
    (Γ : Finset Expr) :
    setLeq leq (Γ ∪ Γ) Γ := by
  simpa only [Finset.union_self] using setLeq_refl (leq := leq) Γ

private theorem setLeq_insert_union_self_of_ordContains {leq : ExprRel} [Std.Refl leq]
    {Γ : Finset Expr} {α : Expr}
    (hα : ordContains leq α Γ) :
    setLeq leq (insert α (Γ ∪ Γ)) Γ := by
  simpa only [Finset.union_self] using setLeq_insert_of_ordContains hα

private theorem not_free_exists_insert_union {x : SVar} {α : Expr}
    {Γ Δ : Finset Expr}
    (hfree : x ∉ freeVars (Γ ∪ Δ)) :
    x ∉ freeVars (insert (exists_ x α) Γ ∪ Δ) := by
  change x ∉ (insert (exists_ x α) Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e)
  change x ∉ (Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e) at hfree
  simpa [Expr.exists_, Finset.biUnion_insert, Finset.union_assoc,
    Finset.union_left_comm, Finset.union_comm] using hfree

private theorem not_free_forall_insert_union {x : SVar} {α : Expr}
    {Γ Δ : Finset Expr}
    (hfree : x ∉ freeVars (Γ ∪ Δ)) :
    x ∉ freeVars (insert (forall_ x α) Γ ∪ Δ) := by
  change x ∉ (insert (forall_ x α) Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e)
  change x ∉ (Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e) at hfree
  simpa [Expr.forall_, Finset.biUnion_insert, Finset.union_assoc,
    Finset.union_left_comm, Finset.union_comm] using hfree

attribute [local simp] isFSet_insert isFSet_empty isFSet_union isFormula_and isFormula_imp isFormula_iff isFormula_neg isFormula_or isFormula_forall isFormula_exists isTerm_epsilon isFormula_substOne isFormula_eq

/-- Recover sorting evidence before applying structural weakening. -/
private theorem orderedWellSorted {leq Γ Δ} (tree : Ordered.ProofTree leq Γ Δ) :
    isFSet Γ ∧ isFSet Δ := by
  induction tree with
  | instSchema σ hΓ hΔ hσ _ _ =>
      constructor <;> intro p hp
      all_goals
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        apply Subst.subst_preserves_hasSort hσ
        first | exact hΓ q hq | exact hΔ q hq
  | rightEpsilon x φ _ hΓ hΔ hx hφ _ _ _ =>
      exact ⟨hΓ, isFSet_insert (isFormula_substOne hx (isTerm_epsilon hx hφ) hφ) hΔ⟩
  | _ =>
      simp_all [isFSet, SubstRule.valid, or_imp, Expr.and, Expr.or, Expr.imp, Expr.iff,
        Expr.neg, Expr.forall_, Expr.exists_, Expr.eq, Expr.top, Expr.bot]

/-- A matched formula can be used as a hypothesis via constructor compatibility. -/
private def sameHypothesis {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq]
    {p q : Expr} (hp : isFormula p) (hq : isFormula q) (h : isSame leq p q) :
    Ordered.ProofTree leq {p} {q} := by
  have hi := RelationCongruence.imp_congr (isSame_refl (leq := leq) p) h
  exact .restateWeaken (isFSet_insert hp isFSet_empty) (isFSet_insert hp isFSet_empty)
    (isFSet_insert hp isFSet_empty) (isFSet_insert hq isFSet_empty) (.hypothesis p hp)
    (by simpa [sequentLeq, sequentToFormula, conjunction, disjunction, foldFormulas] using hi.1)

/-- Cut away each old assumption using a matching assumption already in the target. -/
private theorem clearLeft {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq]
    {Γ target Δ : Finset Expr} (hΓ : isFSet Γ) (ht : isFSet target) (hΔ : isFSet Δ)
    (hmatch : setLeq leq Γ target) (pf : Ordered.ProofTree leq (Γ ∪ target) Δ) :
    Nonempty (Ordered.ProofTree leq target Δ) := by
  induction Γ using Finset.induction_on with
  | empty => exact ⟨by simpa using pf⟩
  | @insert p Γ hnot ih =>
    obtain ⟨q, hq, heq⟩ := hmatch p (Finset.mem_insert_self _ _)
    have hp := hΓ p (Finset.mem_insert_self _ _)
    have hΓrest : isFSet Γ := fun r hr => hΓ r (Finset.mem_insert_of_mem hr)
    have hctx : {q} ∪ (Γ ∪ target) = Γ ∪ target :=
      Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ hq))
    have next := Ordered.ProofTree.cut p
      (isFSet_insert (ht q hq) isFSet_empty) isFSet_empty
      (isFSet_union hΓrest ht) hΔ hp
      (sameHypothesis (ht q hq) hp (OrderLaws.same_symm heq))
      (show Ordered.ProofTree leq (insert p (Γ ∪ target)) Δ from by simpa using pf)
    exact ih hΓrest (fun r hr => hmatch r (Finset.mem_insert_of_mem hr))
      (by simpa only [Finset.insert_empty, hctx, Finset.empty_union] using next)

/-- Cut away each old conclusion using a matching conclusion already in the target. -/
private theorem clearRight {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq]
    {Δ target Γ : Finset Expr} (hΔ : isFSet Δ) (ht : isFSet target) (hΓ : isFSet Γ)
    (hmatch : setLeq leq Δ target) (pf : Ordered.ProofTree leq Γ (Δ ∪ target)) :
    Nonempty (Ordered.ProofTree leq Γ target) := by
  induction Δ using Finset.induction_on with
  | empty => exact ⟨by simpa using pf⟩
  | @insert p Δ hnot ih =>
    obtain ⟨q, hq, heq⟩ := hmatch p (Finset.mem_insert_self _ _)
    have hp := hΔ p (Finset.mem_insert_self _ _)
    have hΔrest : isFSet Δ := fun r hr => hΔ r (Finset.mem_insert_of_mem hr)
    have hctx : (Δ ∪ target) ∪ {q} = Δ ∪ target :=
      Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ hq))
    have next := Ordered.ProofTree.cut p hΓ (isFSet_union hΔrest ht)
      isFSet_empty (isFSet_insert (ht q hq) isFSet_empty) hp
      (show Ordered.ProofTree leq Γ (insert p (Δ ∪ target)) from by simpa using pf)
      (sameHypothesis hp (ht q hq) heq)
    exact ih hΔrest (fun r hr => hmatch r (Finset.mem_insert_of_mem hr))
      (by simpa only [Finset.insert_empty, hctx, Finset.union_empty] using next)

/-- Transport contexts by ordinary weakening and cuts with matched hypotheses. -/
private noncomputable def replaceContexts {leq Γ Δ Γ' Δ'} [Std.Refl leq] [RelationCongruence leq]
    (hΓ' : isFSet Γ') (hΔ' : isFSet Δ') (pf : Ordered.ProofTree leq Γ Δ)
    (hΓ : setLeq leq Γ Γ') (hΔ : setLeq leq Δ Δ') :
    Ordered.ProofTree leq Γ' Δ' := by
  obtain ⟨hsΓ, hsΔ⟩ := orderedWellSorted pf
  have enlarged := Ordered.ProofTree.weakening hsΓ hsΔ
    (isFSet_union hsΓ hΓ') (isFSet_union hsΔ hΔ') pf
    Finset.subset_union_left Finset.subset_union_left
  have left := Classical.choice (clearLeft hsΓ hΓ' (isFSet_union hsΔ hΔ') hΓ enlarged)
  exact Classical.choice (clearRight hsΔ hΔ' hΓ' hΔ left)

private def foldOrFrom (acc : Expr) (prems : List (AnnotatedSequent Expr)) : Expr :=
  (prems.map (·.val)).foldl Expr.or acc

private def foldAndFrom (acc : Expr) (prems : List (AnnotatedSequent Expr)) : Expr :=
  (prems.map (·.val)).foldl Expr.and acc

@[simp] private theorem isFormula_foldOrFrom {acc : Expr} {prems : List (AnnotatedSequent Expr)}
    (hacc : isFormula acc)
    (hprems : ∀ prem ∈ prems, isFormula prem.val) :
    isFormula (foldOrFrom acc prems) := by
  induction prems generalizing acc with
  | nil =>
      simpa [foldOrFrom] using hacc
  | cons prem rest ih =>
      simp [foldOrFrom]
      apply ih
      · exact isFormula_or hacc (hprems prem (by simp))
      · intro q hq
        exact hprems q (by simp [hq])

@[simp] private theorem isFormula_foldAndFrom {acc : Expr} {prems : List (AnnotatedSequent Expr)}
    (hacc : isFormula acc)
    (hprems : ∀ prem ∈ prems, isFormula prem.val) :
    isFormula (foldAndFrom acc prems) := by
  induction prems generalizing acc with
  | nil =>
      simpa [foldAndFrom] using hacc
  | cons prem rest ih =>
      simp [foldAndFrom]
      apply ih
      · exact isFormula_and hacc (hprems prem (by simp))
      · intro q hq
        exact hprems q (by simp [hq])

private def weakenLeftOrPrem {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq]
    {Ω₁ Ω₂ : Finset Expr} (hΩ₁ : isFSet Ω₁) (hΩ₂ : isFSet Ω₂)
    (prem : AnnotatedSequent Expr)
    (hsorted : isFSet prem.pre ∧ isFSet prem.post ∧ isFormula prem.val)
    (hpreserved :
      setLeq leq prem.post Ω₂ ∧
      containedExcept leq prem.pre Ω₁ (prem.val))
    (pf : Ordered.ProofTree leq prem.pre prem.post) :
    Ordered.ProofTree leq (insert prem.val Ω₁) Ω₂ :=
  replaceContexts (isFSet_insert hsorted.2.2 hΩ₁) hΩ₂
    pf
    (setLeq_to_insert_of_containedExcept hpreserved.2)
    hpreserved.1

private def weakenRightAndPrem {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq]
    {Ω₁ Ω₂ : Finset Expr} (hΩ₁ : isFSet Ω₁) (hΩ₂ : isFSet Ω₂)
    (prem : AnnotatedSequent Expr)
    (hsorted : isFSet prem.pre ∧ isFSet prem.post ∧ isFormula prem.val)
    (hpreserved :
      setLeq leq prem.pre Ω₁ ∧
      containedExcept leq prem.post Ω₂ (prem.val))
    (pf : Ordered.ProofTree leq prem.pre prem.post) :
    Ordered.ProofTree leq Ω₁ (insert prem.val Ω₂) :=
  replaceContexts hΩ₁ (isFSet_insert hsorted.2.2 hΩ₂)
    pf
    hpreserved.1
    (setLeq_to_insert_of_containedExcept hpreserved.2)

private def foldLeftOrOrdered {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq]
    {Ω₁ Ω₂ : Finset Expr} (hΩ₁ : isFSet Ω₁) (hΩ₂ : isFSet Ω₂)
    (acc : Expr) (hacc : isFormula acc)
    (pfacc : Ordered.ProofTree leq (insert acc Ω₁) Ω₂)
    (rest : List (AnnotatedSequent Expr))
    (hsortedRest :
      ∀ prem ∈ rest, isFSet prem.pre ∧ isFSet prem.post ∧ isFormula prem.val)
    (hstdRest :
      ∀ prem ∈ rest, Ordered.ProofTree leq prem.pre prem.post)
    (hpreservedRest :
      ∀ prem ∈ rest,
        setLeq leq prem.post Ω₂ ∧
        containedExcept leq prem.pre Ω₁ (prem.val)) :
    Ordered.ProofTree leq (insert (foldOrFrom acc rest) Ω₁) Ω₂ := by
  induction rest generalizing acc with
  | nil => exact pfacc
  | cons prem rest ih =>
      have hs := hsortedRest prem (by simp)
      have hp := weakenLeftOrPrem hΩ₁ hΩ₂ prem hs
        (hpreservedRest prem (by simp)) (hstdRest prem (by simp))
      have combined : Ordered.ProofTree leq (insert (or acc prem.val) Ω₁) Ω₂ := by
        simpa only [Finset.union_self] using
          (Ordered.ProofTree.leftOr acc prem.val
            hΩ₁ hΩ₂ hΩ₁ hΩ₂ hacc hs.2.2 pfacc hp)
      simpa [foldOrFrom] using
        ih (or acc prem.val) (isFormula_or hacc hs.2.2) combined
          (fun q hq => hsortedRest q (by simp [hq]))
          (fun q hq => hstdRest q (by simp [hq]))
          (fun q hq => hpreservedRest q (by simp [hq]))

private def foldRightAndOrdered {leq : ExprRel} [Std.Refl leq] [RelationCongruence leq]
    {Ω₁ Ω₂ : Finset Expr} (hΩ₁ : isFSet Ω₁) (hΩ₂ : isFSet Ω₂)
    (acc : Expr) (hacc : isFormula acc)
    (pfacc : Ordered.ProofTree leq Ω₁ (insert acc Ω₂))
    (rest : List (AnnotatedSequent Expr))
    (hsortedRest :
      ∀ prem ∈ rest, isFSet prem.pre ∧ isFSet prem.post ∧ isFormula prem.val)
    (hstdRest :
      ∀ prem ∈ rest, Ordered.ProofTree leq prem.pre prem.post)
    (hpreservedRest :
      ∀ prem ∈ rest,
        setLeq leq prem.pre Ω₁ ∧
        containedExcept leq prem.post Ω₂ (prem.val)) :
    Ordered.ProofTree leq Ω₁ (insert (foldAndFrom acc rest) Ω₂) := by
  induction rest generalizing acc with
  | nil => exact pfacc
  | cons prem rest ih =>
      have hs := hsortedRest prem (by simp)
      have hp := weakenRightAndPrem hΩ₁ hΩ₂ prem hs
        (hpreservedRest prem (by simp)) (hstdRest prem (by simp))
      have combined : Ordered.ProofTree leq Ω₁ (insert (and acc prem.val) Ω₂) := by
        simpa only [Finset.union_self] using
          (Ordered.ProofTree.rightAnd acc prem.val
            hΩ₁ hΩ₂ hΩ₁ hΩ₂ hacc hs.2.2 pfacc hp)
      simpa [foldAndFrom] using
        ih (and acc prem.val) (isFormula_and hacc hs.2.2) combined
          (fun q hq => hsortedRest q (by simp [hq]))
          (fun q hq => hstdRest q (by simp [hq]))
          (fun q hq => hpreservedRest q (by simp [hq]))

/-- Translate strict rule applications to their weakened counterparts. -/
def orderedToWeakened {leq Γ Δ} [Std.Refl leq] :
    Ordered.ProofTree leq Γ Δ →
    Weakened.ProofTree leq Γ Δ
  | .leftFalse => .leftFalse
  | .rightTrue => .restateTrue isFSet_empty (isFSet_insert (by rfl) isFSet_empty)
      (by simp [sequentToFormula, disjunction, foldFormulas])
  | .weakening hΓ hΔ hΓ' hΔ' pf hsubΓ hsubΔ =>
      .cut (Γ₁ := ∅) (Γ₂ := {top}) top isFSet_empty (isFSet_insert (by rfl) isFSet_empty)
        (.restateTrue isFSet_empty (isFSet_insert (by rfl) isFSet_empty)
          (by simp [sequentToFormula, disjunction, foldFormulas]))
        hΓ hΔ (orderedToWeakened pf) hΓ' hΔ' (by rfl)
        (by intro p hp; simp at hp)
        (fun p hp => ⟨p, hsubΔ hp, isSame_refl _⟩)
        (by intro p hp; have : p = top := Finset.mem_singleton.mp hp; subst p; exact Or.inr (isSame_refl top))
        (fun p hp => Or.inl ⟨p, hsubΓ hp, isSame_refl _⟩)
  | .restateWeaken hΓ hΔ hΓ' hΔ' pf hle =>
      .weakening hΓ hΔ hΓ' hΔ' (orderedToWeakened pf) hle
  | .hypothesis φ hφ =>
      .hypothesis φ (isFSet_insert hφ isFSet_empty) (isFSet_insert hφ isFSet_empty) hφ
        (ordContains_refl φ ∅) (ordContains_refl φ ∅)
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      .cut φ
        hΓ (isFSet_insert hφ hΔ)
        (orderedToWeakened pf₁)
        (isFSet_insert hφ hΩ) hΞ
        (orderedToWeakened pf₂)
        (isFSet_union hΓ hΩ) (isFSet_union hΔ hΞ)
        hφ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      .leftAnd φ ψ
        (isFSet_insert hφ (isFSet_insert hψ hΓ)) hΔ
        (orderedToWeakened pf)
        (isFSet_insert (isFormula_and hφ hψ) hΓ) hΔ
        hφ hψ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .leftOr (Γ := Γ₁) (Ω := Ω₁) (Δ := Δ₁) (Ξ := Ξ₁) φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      let prems : List (AnnotatedSequent Expr) :=
        [
          { pre := insert φ Γ₁, post := Δ₁, val := φ },
          { pre := insert ψ Ω₁, post := Ξ₁, val := ψ }
        ]
      .leftOr (prems := prems)
        (Ω₁ := insert (or φ ψ) (Γ₁ ∪ Ω₁)) (Ω₂ := Δ₁ ∪ Ξ₁)
        (by simp [prems])
        (isFSet_insert (isFormula_or hφ hψ) (isFSet_union hΓ hΩ))
        (isFSet_union hΔ hΞ)
        (by
          intro prem hprem
          simp only [prems, List.mem_cons, List.not_mem_nil, or_false] at hprem
          rcases hprem with rfl | rfl
          · exact ⟨isFSet_insert hφ hΓ, hΔ, hφ⟩
          · exact ⟨isFSet_insert hψ hΩ, hΞ, hψ⟩)
        (by
          intro prem hprem
          simp only [prems, List.mem_cons, List.not_mem_nil, or_false] at hprem
          by_cases h : prem = { pre := insert φ Γ₁, post := Δ₁, val := φ }
          · subst prem
            exact orderedToWeakened pf₁
          · have h' := hprem.resolve_left h
            subst prem
            exact orderedToWeakened pf₂)
        (by
          intro prem hprem
          simp only [prems, List.mem_cons, List.not_mem_nil, or_false] at hprem
          rcases hprem with rfl | rfl <;> dsimp <;> lisa_context)
        (by dsimp [prems]; lisa_context)
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .leftImp φ ψ
        hΓ (isFSet_insert hφ hΔ)
        (orderedToWeakened pf₁)
        (isFSet_insert hψ hΩ) hΞ
        (orderedToWeakened pf₂)
        (isFSet_insert (isFormula_imp hφ hψ) (isFSet_union hΓ hΩ)) (isFSet_union hΔ hΞ)
        hφ hψ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      .leftIff φ ψ
        (isFSet_insert (isFormula_imp hφ hψ)
          (isFSet_insert (isFormula_imp hψ hφ) hΓ))
        hΔ
        (orderedToWeakened pf)
        (isFSet_insert (isFormula_iff hφ hψ) hΓ) hΔ
        hφ hψ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .leftNot φ hΓ hΔ hφ pf =>
      .leftNot φ
        hΓ (isFSet_insert hφ hΔ)
        (orderedToWeakened pf)
        (isFSet_insert (isFormula_neg hφ) hΓ) hΔ
        hφ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      .leftForall x φ t
        (isFSet_insert (isFormula_substOne hx ht hφ) hΓ) hΔ
        (orderedToWeakened pf)
        (isFSet_insert (isFormula_forall hx hφ) hΓ) hΔ
        hx hφ ht
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      .leftExists x φ
        (isFSet_insert hφ hΓ) hΔ
        (orderedToWeakened pf)
        (isFSet_insert (isFormula_exists hx hφ) hΓ) hΔ
        hx hφ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
        hfree
  | .rightAnd (Γ := Γ₁) (Ω := Ω₁) (Δ := Δ₁) (Ξ := Ξ₁) φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      let prems : List (AnnotatedSequent Expr) :=
        [
          { pre := Γ₁, post := insert φ Δ₁, val := φ },
          { pre := Ω₁, post := insert ψ Ξ₁, val := ψ }
        ]
      .rightAnd (prems := prems)
        (Ω₁ := Γ₁ ∪ Ω₁) (Ω₂ := insert (and φ ψ) (Δ₁ ∪ Ξ₁))
        (by simp [prems])
        (isFSet_union hΓ hΩ)
        (isFSet_insert (isFormula_and hφ hψ) (isFSet_union hΔ hΞ))
        (by
          intro prem hprem
          simp only [prems, List.mem_cons, List.not_mem_nil, or_false] at hprem
          rcases hprem with rfl | rfl
          · exact ⟨hΓ, isFSet_insert hφ hΔ, hφ⟩
          · exact ⟨hΩ, isFSet_insert hψ hΞ, hψ⟩)
        (by
          intro prem hprem
          simp only [prems, List.mem_cons, List.not_mem_nil, or_false] at hprem
          by_cases h : prem = { pre := Γ₁, post := insert φ Δ₁, val := φ }
          · subst prem
            exact orderedToWeakened pf₁
          · have h' := hprem.resolve_left h
            subst prem
            exact orderedToWeakened pf₂)
        (by
          intro prem hprem
          simp only [prems, List.mem_cons, List.not_mem_nil, or_false] at hprem
          rcases hprem with rfl | rfl <;> dsimp <;> lisa_context)
        (by dsimp [prems]; lisa_context)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      .rightOr φ ψ
        hΓ (isFSet_insert hφ (isFSet_insert hψ hΔ))
        (orderedToWeakened pf)
        hΓ (isFSet_insert (isFormula_or hφ hψ) hΔ)
        hφ hψ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      .rightImp φ ψ
        (isFSet_insert hφ hΓ) (isFSet_insert hψ hΔ)
        (orderedToWeakened pf)
        hΓ (isFSet_insert (isFormula_imp hφ hψ) hΔ)
        hφ hψ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      .rightIff φ ψ
        hΓ (isFSet_insert (isFormula_imp hφ hψ) hΔ)
        (orderedToWeakened pf₁)
        hΩ (isFSet_insert (isFormula_imp hψ hφ) hΞ)
        (orderedToWeakened pf₂)
        (isFSet_union hΓ hΩ) (isFSet_insert (isFormula_iff hφ hψ) (isFSet_union hΔ hΞ))
        hφ hψ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .rightNot φ hΓ hΔ hφ pf =>
      .rightNot φ
        (isFSet_insert hφ hΓ) hΔ
        (orderedToWeakened pf)
        hΓ (isFSet_insert (isFormula_neg hφ) hΔ)
        hφ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      .rightForall x φ
        hΓ (isFSet_insert hφ hΔ)
        (orderedToWeakened pf)
        hΓ (isFSet_insert (isFormula_forall hx hφ) hΔ)
        hx hφ
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
        (by
          have hsets : insert (forall_ x φ) Γ ∪ Δ = Γ ∪ insert (forall_ x φ) Δ := by
            ext χ
            simp [or_assoc, or_comm]
          simpa [hsets] using hfree)
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      .rightExists x φ t
        hΓ (isFSet_insert (isFormula_substOne hx ht hφ) hΔ)
        (orderedToWeakened pf)
        hΓ (isFSet_insert (isFormula_exists hx hφ) hΔ)
        hx hφ ht
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      .rightEpsilon x φ t
        hΓ (isFSet_insert (isFormula_substOne hx ht hφ) hΔ)
        (orderedToWeakened pf)
        hΓ (isFSet_insert (isFormula_substOne hx (isTerm_epsilon hx hφ) hφ) hΔ)
        hx hφ ht
        (by lisa_context)
        (by lisa_context)
        (by lisa_context)
  | .leftRefl t hΓ hΔ ht pf =>
      .leftRefl t t
        (isFSet_insert (isFormula_eq ht ht) hΓ) hΔ
        (orderedToWeakened pf)
        hΓ hΔ
        ht ht (isSame_refl t)
        (by lisa_context)
        (by lisa_context)
  | .rightRefl t ht =>
      .rightRefl t t
        (show isFSet (∅ : Finset Expr) from by
          intro φ hφ
          simp at hφ)
        (isFSet_insert (isFormula_eq ht ht) (show isFSet (∅ : Finset Expr) from by
          intro φ hφ
          simp at hφ))
        ht ht (isSame_refl t)
        (ordContains_refl (eq t t) ∅)
  | .leftSubst r hΓ hΔ hΘ hΞ hv hf p q =>
      .leftSubst r (isFSet_insert hv.2.2.2.1 hΓ) hΔ (orderedToWeakened p)
        hΘ hΞ (orderedToWeakened q)
        (isFSet_insert hv.2.2.2.2 (isFSet_union hΓ hΘ)) (isFSet_union hΔ hΞ)
        hv hf (by lisa_context) (by lisa_context) (by lisa_context)
        (by lisa_context) (by lisa_context)
  | .rightSubst r hΓ hΔ hΘ hΞ hv hf p q =>
      .rightSubst r hΓ (isFSet_insert hv.2.2.2.1 hΔ) (orderedToWeakened p)
        hΘ hΞ (orderedToWeakened q)
        (isFSet_union hΓ hΘ) (isFSet_insert hv.2.2.2.2 (isFSet_union hΔ hΞ))
        hv hf (by lisa_context) (by lisa_context) (by lisa_context)
        (by lisa_context) (by lisa_context)
  | .instSchema σ hΓ hΔ hσ pf =>
      .instSchema σ
        hΓ hΔ
        (orderedToWeakened pf)
        (by
          intro φ hφ
          simp only [Finset.mem_image] at hφ
          rcases hφ with ⟨ψ, hψ, rfl⟩
          exact Subst.subst_preserves_hasSort hσ (hΓ ψ hψ))
        (by
          intro φ hφ
          simp only [Finset.mem_image] at hφ
          rcases hφ with ⟨ψ, hψ, rfl⟩
          exact Subst.subst_preserves_hasSort hσ (hΔ ψ hψ))
        hσ
        ⟨setLeq_refl _, setLeq_refl _⟩

/-- Derive the convenience rule directly from truth and whole-sequent restatement. -/
private def restateTrueOrdered {leq : ExprRel}
    {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ)
    (h : isSame leq (sequentToFormula Γ Δ) top) : Ordered.ProofTree leq Γ Δ :=
  .restateWeaken
    isFSet_empty (isFSet_insert (by rfl) isFSet_empty)
    hΓ hΔ .rightTrue
    (by simpa [sequentLeq, sequentToFormula, disjunction, foldFormulas] using h.2)

/-- Restore strict premise contexts, apply the rule, and replace its conclusion contexts. -/
def weakenedToOrdered {leq Γ Δ} [Std.Refl leq] [RelationCongruence leq] :
    Weakened.ProofTree leq Γ Δ →
    Ordered.ProofTree leq Γ Δ
  | .leftFalse => .leftFalse
  | .restate hΓ hΔ hΓ' hΔ' pf hle₁ _ =>
      .restateWeaken hΓ hΔ hΓ' hΔ' (weakenedToOrdered pf) hle₁
  | .weakening hΓ hΔ hΓ' hΔ' pf hle =>
      .restateWeaken hΓ hΔ hΓ' hΔ' (weakenedToOrdered pf) hle
  | .restateTrue hΓ hΔ h => restateTrueOrdered hΓ hΔ h
  | .hypothesis α hΩ₁ hΩ₂ hα hleft hright =>
      replaceContexts hΩ₁ hΩ₂
        (.hypothesis α hα)
        (setLeq_singleton_of_ordContains hleft)
        (setLeq_singleton_of_ordContains hright)
  | .cut (Ω₁ := Ω₁) (Ω₂ := Ω₂) α _ _ pf₁ _ _ pf₂ hΩ₁ hΩ₂ hα hsub₁ hsub₂ hrem₁ hrem₂ =>
      let pf₁' : Ordered.ProofTree leq Ω₁ (insert α Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert hα hΩ₂)
          (weakenedToOrdered pf₁)
          hsub₁
          (setLeq_to_insert_of_containedExcept hrem₁)
      let pf₂' : Ordered.ProofTree leq (insert α Ω₁) Ω₂ :=
        replaceContexts (isFSet_insert hα hΩ₁) hΩ₂
          (weakenedToOrdered pf₂)
          (setLeq_to_insert_of_containedExcept hrem₂)
          hsub₂
      replaceContexts hΩ₁ hΩ₂
        (.cut α hΩ₁ hΩ₂ hΩ₁ hΩ₂ hα pf₁' pf₂')
        (setLeq_union_self Ω₁)
        (setLeq_union_self Ω₂)
  | .leftAnd (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β _ _ pf hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq (insert α (insert β Ω₁)) Ω₂ :=
        replaceContexts (isFSet_insert hα (isFSet_insert hβ hΩ₁)) hΩ₂
          (weakenedToOrdered pf)
          (setLeq_to_insert₂_of_containedExceptEither hrem)
          hsub
      replaceContexts hΩ₁ hΩ₂
        (.leftAnd α β hΩ₁ hΩ₂ hα hβ pf')
        (setLeq_insert_of_ordContains hadd)
        (setLeq_refl Ω₂)
  | .leftOr (prems := prems) (Ω₁ := Ω₁) (Ω₂ := Ω₂) hne hΩ₁ hΩ₂ hsorted hprems hpreserved hadd =>
      match prems with
      | [] => False.elim (hne rfl)
      | prem :: rest =>
          let hpremSorted :
              isFSet prem.pre ∧ isFSet prem.post ∧ isFormula prem.val := by
            simpa using hsorted prem (by simp)
          let hpremPreserved :
              setLeq leq prem.post Ω₂ ∧
              containedExcept leq prem.pre Ω₁ (prem.val) := by
            simpa using hpreserved prem (by simp)
          let firstPf : Ordered.ProofTree leq (insert prem.val Ω₁) Ω₂ :=
            weakenLeftOrPrem hΩ₁ hΩ₂ prem hpremSorted hpremPreserved
              (weakenedToOrdered (hprems prem (by simp)))
          let foldedPf : Ordered.ProofTree leq (insert (foldOrFrom prem.val rest) Ω₁) Ω₂ :=
            foldLeftOrOrdered hΩ₁ hΩ₂ prem.val hpremSorted.2.2 firstPf rest
              (by
                intro q hq
                exact hsorted q (by simp [hq]))
              (by
                intro q hq
                exact weakenedToOrdered (hprems q (by simp [hq])))
              (by
                intro q hq
                exact hpreserved q (by simp [hq]))
          replaceContexts hΩ₁ hΩ₂
            foldedPf
            (setLeq_insert_of_ordContains (by
                simpa [foldOrFrom] using hadd))
            (setLeq_refl Ω₂)
  | .leftImp (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β _ _ pf₁ _ _ pf₂ hΩ₁ hΩ₂ hα hβ hsub₁ hsub₂ hrem₁ hrem₂ hadd =>
      let pf₁' : Ordered.ProofTree leq Ω₁ (insert α Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert hα hΩ₂)
          (weakenedToOrdered pf₁)
          hsub₁
          (setLeq_to_insert_of_containedExcept hrem₁)
      let pf₂' : Ordered.ProofTree leq (insert β Ω₁) Ω₂ :=
        replaceContexts (isFSet_insert hβ hΩ₁) hΩ₂
          (weakenedToOrdered pf₂)
          (setLeq_to_insert_of_containedExcept hrem₂)
          hsub₂
      replaceContexts hΩ₁ hΩ₂
        (.leftImp α β hΩ₁ hΩ₂ hΩ₁ hΩ₂ hα hβ pf₁' pf₂')
        (setLeq_insert_union_self_of_ordContains hadd)
        (setLeq_union_self Ω₂)
  | .leftIff (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β _ _ pf hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq (insert (imp α β) (insert (imp β α) Ω₁)) Ω₂ :=
        replaceContexts (isFSet_insert (isFormula_imp hα hβ)
            (isFSet_insert (isFormula_imp hβ hα) hΩ₁)) hΩ₂
          (weakenedToOrdered pf)
          (setLeq_to_insert₂_of_containedExceptEither hrem)
          hsub
      replaceContexts hΩ₁ hΩ₂
        (.leftIff α β hΩ₁ hΩ₂ hα hβ pf')
        (setLeq_insert_of_ordContains hadd)
        (setLeq_refl Ω₂)
  | .leftNot (Ω₁ := Ω₁) (Ω₂ := Ω₂) α _ _ pf hΩ₁ hΩ₂ hα hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq Ω₁ (insert α Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert hα hΩ₂)
          (weakenedToOrdered pf)
          hsub
          (setLeq_to_insert_of_containedExcept hrem)
      replaceContexts hΩ₁ hΩ₂
        (.leftNot α hΩ₁ hΩ₂ hα pf')
        (setLeq_insert_of_ordContains hadd)
        (setLeq_refl Ω₂)
  | .leftForall (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α t _ _ pf hΩ₁ hΩ₂ hx hα ht hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq (insert (substOne x t α) Ω₁) Ω₂ :=
        replaceContexts (isFSet_insert (isFormula_substOne hx ht hα) hΩ₁) hΩ₂
          (weakenedToOrdered pf)
          (setLeq_to_insert_of_containedExcept hrem)
          hsub
      replaceContexts hΩ₁ hΩ₂
        (.leftForall x α t hΩ₁ hΩ₂ hx hα ht pf')
        (setLeq_insert_of_ordContains hadd)
        (setLeq_refl Ω₂)
  | .leftExists (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α _ _ pf hΩ₁ hΩ₂ hx hα hsub hrem hadd hfree =>
      let pf' : Ordered.ProofTree leq (insert α Ω₁) Ω₂ :=
        replaceContexts (isFSet_insert hα hΩ₁) hΩ₂
          (weakenedToOrdered pf)
          (setLeq_to_insert_of_containedExcept hrem)
          hsub
      replaceContexts hΩ₁ hΩ₂
        (.leftExists x α hΩ₁ hΩ₂ hx hα pf'
          (not_free_exists_insert_union hfree))
        (setLeq_insert_of_ordContains hadd)
        (setLeq_refl Ω₂)
  | .rightAnd (prems := prems) (Ω₁ := Ω₁) (Ω₂ := Ω₂) hne hΩ₁ hΩ₂ hsorted hprems hpreserved hadd =>
      match prems with
      | [] => False.elim (hne rfl)
      | prem :: rest =>
          let hpremSorted :
              isFSet prem.pre ∧ isFSet prem.post ∧ isFormula prem.val := by
            simpa using hsorted prem (by simp)
          let hpremPreserved :
              setLeq leq prem.pre Ω₁ ∧
              containedExcept leq prem.post Ω₂ (prem.val) := by
            simpa using hpreserved prem (by simp)
          let firstPf : Ordered.ProofTree leq Ω₁ (insert prem.val Ω₂) :=
            weakenRightAndPrem hΩ₁ hΩ₂ prem hpremSorted hpremPreserved
              (weakenedToOrdered (hprems prem (by simp)))
          let foldedPf : Ordered.ProofTree leq Ω₁ (insert (foldAndFrom prem.val rest) Ω₂) :=
            foldRightAndOrdered hΩ₁ hΩ₂ prem.val hpremSorted.2.2 firstPf rest
              (by
                intro q hq
                exact hsorted q (by simp [hq]))
              (by
                intro q hq
                exact weakenedToOrdered (hprems q (by simp [hq])))
              (by
                intro q hq
                exact hpreserved q (by simp [hq]))
          replaceContexts hΩ₁ hΩ₂
            foldedPf
            (setLeq_refl Ω₁)
            (setLeq_insert_of_ordContains (by
                simpa [foldAndFrom] using hadd))
  | .rightOr (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β _ _ pf hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq Ω₁ (insert α (insert β Ω₂)) :=
        replaceContexts hΩ₁ (isFSet_insert hα (isFSet_insert hβ hΩ₂))
          (weakenedToOrdered pf)
          hsub
          (setLeq_to_insert₂_of_containedExceptEither hrem)
      replaceContexts hΩ₁ hΩ₂
        (.rightOr α β hΩ₁ hΩ₂ hα hβ pf')
        (setLeq_refl Ω₁)
        (setLeq_insert_of_ordContains hadd)
  | .rightImp (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β _ _ pf hΩ₁ hΩ₂ hα hβ hrem₁ hrem₂ hadd =>
      let pf' : Ordered.ProofTree leq (insert α Ω₁) (insert β Ω₂) :=
        replaceContexts (isFSet_insert hα hΩ₁) (isFSet_insert hβ hΩ₂)
          (weakenedToOrdered pf)
          (setLeq_to_insert_of_containedExcept hrem₁)
          (setLeq_to_insert_of_containedExcept hrem₂)
      replaceContexts hΩ₁ hΩ₂
        (.rightImp α β hΩ₁ hΩ₂ hα hβ pf')
        (setLeq_refl Ω₁)
        (setLeq_insert_of_ordContains hadd)
  | .rightIff (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β _ _ pf₁ _ _ pf₂ hΩ₁ hΩ₂ hα hβ hsub₁ hsub₂ hrem₁ hrem₂ hadd
      =>
      let pf₁' : Ordered.ProofTree leq Ω₁ (insert (imp α β) Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert (isFormula_imp hα hβ) hΩ₂)
          (weakenedToOrdered pf₁)
          hsub₁
          (setLeq_to_insert_of_containedExcept hrem₁)
      let pf₂' : Ordered.ProofTree leq Ω₁ (insert (imp β α) Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert (isFormula_imp hβ hα) hΩ₂)
          (weakenedToOrdered pf₂)
          hsub₂
          (setLeq_to_insert_of_containedExcept hrem₂)
      replaceContexts hΩ₁ hΩ₂
        (.rightIff α β hΩ₁ hΩ₂ hΩ₁ hΩ₂ hα hβ pf₁' pf₂')
        (setLeq_union_self Ω₁)
        (setLeq_insert_union_self_of_ordContains hadd)
  | .rightNot (Ω₁ := Ω₁) (Ω₂ := Ω₂) α _ _ pf hΩ₁ hΩ₂ hα hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq (insert α Ω₁) Ω₂ :=
        replaceContexts (isFSet_insert hα hΩ₁) hΩ₂
          (weakenedToOrdered pf)
          (setLeq_to_insert_of_containedExcept hrem)
          hsub
      replaceContexts hΩ₁ hΩ₂
        (.rightNot α hΩ₁ hΩ₂ hα pf')
        (setLeq_refl Ω₁)
        (setLeq_insert_of_ordContains hadd)
  | .rightForall (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α _ _ pf hΩ₁ hΩ₂ hx hα hsub hrem hadd hfree =>
      let pf' : Ordered.ProofTree leq Ω₁ (insert α Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert hα hΩ₂)
          (weakenedToOrdered pf)
          hsub
          (setLeq_to_insert_of_containedExcept hrem)
      replaceContexts hΩ₁ hΩ₂
        (.rightForall x α hΩ₁ hΩ₂ hx hα pf'
          (not_free_forall_insert_union hfree))
        (setLeq_refl Ω₁)
        (setLeq_insert_of_ordContains hadd)
  | .rightExists (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α t _ _ pf hΩ₁ hΩ₂ hx hα ht hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq Ω₁ (insert (substOne x t α) Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert (isFormula_substOne hx ht hα) hΩ₂)
          (weakenedToOrdered pf)
          hsub
          (setLeq_to_insert_of_containedExcept hrem)
      replaceContexts hΩ₁ hΩ₂
        (.rightExists x α t hΩ₁ hΩ₂ hx hα ht pf')
        (setLeq_refl Ω₁)
        (setLeq_insert_of_ordContains hadd)
  | .rightEpsilon (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α t _ _ pf hΩ₁ hΩ₂ hx hα ht hsub hrem hadd =>
      let pf' : Ordered.ProofTree leq Ω₁ (insert (substOne x t α) Ω₂) :=
        replaceContexts hΩ₁ (isFSet_insert (isFormula_substOne hx ht hα) hΩ₂)
          (weakenedToOrdered pf)
          hsub
          (setLeq_to_insert_of_containedExcept hrem)
      replaceContexts hΩ₁ hΩ₂
        (.rightEpsilon x α t hΩ₁ hΩ₂ hx hα ht pf')
        (setLeq_refl Ω₁)
        (setLeq_insert_of_ordContains hadd)
  | .leftRefl s t _ _ pf hΩ₁ hΩ₂ hs ht heq hsub hrem =>
      let same := RelationCongruence.refl_eq hs ht heq
      let prem := replaceContexts (isFSet_insert (isFormula_eq hs ht) hΩ₁) hΩ₂
        (weakenedToOrdered pf)
        (setLeq_to_insert_of_containedExcept hrem)
        hsub
      let strictPrem := replaceContexts (isFSet_insert (isFormula_eq hs hs) hΩ₁) hΩ₂ prem
        (setLeq_insert_of_same (OrderLaws.same_symm same)) (setLeq_refl _)
      .leftRefl s hΩ₁ hΩ₂ hs strictPrem
  | .rightRefl (Ω₁ := Ω₁) s t hΩ₁ hΩ₂ hs ht heq hadd =>
      let same := RelationCongruence.refl_eq hs ht heq
      let refl := .rightRefl s hs
      let replay : Ordered.ProofTree leq ∅ {eq s t} := replaceContexts
        isFSet_empty (isFSet_insert (isFormula_eq hs ht) isFSet_empty) refl
        (setLeq_empty ∅) (setLeq_singleton_of_same same)
      replaceContexts hΩ₁ hΩ₂
        replay
        (setLeq_empty Ω₁)
        (setLeq_singleton_of_ordContains hadd)
  | .leftSubst (Ω₁ := Ω₁) (Ω₂ := Ω₂) r _ _ p hΘ hΞ q
      hΩ₁ hΩ₂ hv hf hleft hright hadd hΘsub hΞsub =>
      let prem := replaceContexts (isFSet_insert hv.2.2.2.1 hΩ₁) hΩ₂
        (weakenedToOrdered p) (setLeq_to_insert_of_containedExcept hleft) hright
      let result := Ordered.ProofTree.leftSubst r hΩ₁ hΩ₂ hΘ hΞ hv hf
        prem (weakenedToOrdered q)
      replaceContexts hΩ₁ hΩ₂ result
        (by
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact hadd
          · rcases Finset.mem_union.mp he with he | he
            · exact ⟨e, he, isSame_refl e⟩
            · exact hΘsub e he)
        (by
          intro e he
          rcases Finset.mem_union.mp he with he | he
          · exact ⟨e, he, isSame_refl e⟩
          · exact hΞsub e he)
  | .rightSubst (Ω₁ := Ω₁) (Ω₂ := Ω₂) r _ _ p hΘ hΞ q
      hΩ₁ hΩ₂ hv hf hleft hright hadd hΘsub hΞsub =>
      let prem := replaceContexts hΩ₁ (isFSet_insert hv.2.2.2.1 hΩ₂)
        (weakenedToOrdered p) hleft (setLeq_to_insert_of_containedExcept hright)
      let result := Ordered.ProofTree.rightSubst r hΩ₁ hΩ₂ hΘ hΞ hv hf
        prem (weakenedToOrdered q)
      replaceContexts hΩ₁ hΩ₂ result
        (by
          intro e he
          rcases Finset.mem_union.mp he with he | he
          · exact ⟨e, he, isSame_refl e⟩
          · exact hΘsub e he)
        (by
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact hadd
          · rcases Finset.mem_union.mp he with he | he
            · exact ⟨e, he, isSame_refl e⟩
            · exact hΞsub e he)
  | .instSchema σ hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hσ hle =>
      replaceContexts hΩ₁ hΩ₂
        (.instSchema σ hΓ₁ hΓ₂ hσ (weakenedToOrdered pf))
        hle.1
        hle.2

theorem ordered_eq_weakened (leq : ExprRel) [Std.Refl leq] [RelationCongruence leq] (Γ Δ : Finset Expr) :
    Nonempty (Ordered.ProofTree leq Γ Δ) ↔
    Nonempty (Weakened.ProofTree leq Γ Δ) := by
  constructor <;> intro ⟨pf⟩
  · exact ⟨orderedToWeakened pf⟩
  · exact ⟨weakenedToOrdered pf⟩
