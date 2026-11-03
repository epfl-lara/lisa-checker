import Lisa.Checker.Encoding

/-! Sound positive tests. Failure means that this checker did not establish the
condition; it never produces a proof of its negation. -/
namespace Imported.Checker
open Lisa Expr Orthologic

structure Test (P : Prop) where
  ok : Bool
  sound : ok = true → P

def Test.map (t : Test P) (f : P → Q) : Test Q := ⟨t.ok, fun h => f (t.sound h)⟩

class Testable (P : Prop) where
  test : Test P

def verify (P : Prop) [Testable P] : Test P := Testable.test

instance (priority := 100) [Decidable P] : Testable P :=
  ⟨⟨decide P, of_decide_eq_true⟩⟩

instance [Testable P] [Testable Q] : Testable (P ∧ Q) :=
  ⟨⟨(verify P).ok && (verify Q).ok, fun h => by
    simp only [Bool.and_eq_true] at h
    exact ⟨(verify P).sound h.1, (verify Q).sound h.2⟩⟩⟩

instance [Testable P] [Testable Q] : Testable (P ∨ Q) :=
  ⟨⟨(verify P).ok || (verify Q).ok, fun h => by
    simp only [Bool.or_eq_true] at h
    exact h.elim (fun h => Or.inl ((verify P).sound h)) (fun h => Or.inr ((verify Q).sound h))⟩⟩

instance [DecidableEq α] (s : Finset α) (P : α → Prop) [∀ x, Testable (P x)] :
    Testable (∀ x ∈ s, P x) :=
  ⟨⟨decide (∀ x ∈ s, (verify (P x)).ok = true), fun h x hx =>
    (verify (P x)).sound (of_decide_eq_true h x hx)⟩⟩

instance [DecidableEq α] (s : Finset α) (P : α → Prop) [∀ x, Testable (P x)] :
    Testable (∃ x ∈ s, P x) :=
  ⟨⟨decide (∃ x ∈ s, (verify (P x)).ok = true), fun h => by
    obtain ⟨x, hx, hp⟩ := of_decide_eq_true h
    exact ⟨x, hx, (verify (P x)).sound hp⟩⟩⟩

instance (s : List α) (P : α → Prop) [∀ x, Testable (P x)] :
    Testable (∀ x ∈ s, P x) :=
  ⟨⟨decide (∀ x ∈ s, (verify (P x)).ok = true), fun h x hx =>
    (verify (P x)).sound (of_decide_eq_true h x hx)⟩⟩

instance (p : Expr) : Decidable p.wellSorted := inferInstanceAs (Decidable p.sort.isSome)
instance (p : Expr) : Decidable (isFormula p) := inferInstanceAs (Decidable (p.sort = some prop))
instance (p : Expr) : Decidable (isTerm p) := inferInstanceAs (Decidable (p.sort = some ind))
instance (Γ : Finset Expr) : Decidable (isFSet Γ) :=
  inferInstanceAs (Decidable (∀ p ∈ Γ, isFormula p))

private def decideSubst : (σ : Subst) → Decidable σ.wellSorted
  | .nil => isTrue trivial
  | .cons _ _ rest => @instDecidableAnd _ _ (inferInstanceAs (Decidable (_ = _))) (decideSubst rest)
instance (σ : Subst) : Decidable σ.wellSorted := decideSubst σ

instance (p q : Expr) : Testable (isSame ProofRelation p q) := ⟨
  if h : p = q then ⟨true, fun _ => by subst q; exact ⟨OrderLaws.self_le _, OrderLaws.self_le _⟩⟩
  else ⟨decide (Cached.isSame p q = some true), fun h => ProofRelation.of_same (of_decide_eq_true h)⟩⟩

instance (p q : Expr) : Testable (ProofRelation p q) := ⟨
  ⟨decide (Cached.isImplying p q = some true), fun h => ProofRelation.of_implying (of_decide_eq_true h)⟩⟩

instance (p : Expr) (Γ : Finset Expr) : Testable (ordContains ProofRelation p Γ) :=
  inferInstanceAs (Testable (∃ q ∈ Γ, isSame ProofRelation p q))

instance (Γ Δ : Finset Expr) : Testable (setLeq ProofRelation Γ Δ) :=
  inferInstanceAs (Testable (∀ p ∈ Γ, ∃ q ∈ Δ, isSame ProofRelation p q))

instance (Γ Δ : Finset Expr) (p : Expr) : Testable (containedExcept ProofRelation Γ Δ p) :=
  inferInstanceAs (Testable (∀ q ∈ Γ, (∃ r ∈ Δ, isSame ProofRelation q r) ∨ isSame ProofRelation q p))

instance (Γ Δ : Finset Expr) (p q : Expr) : Testable (containedExceptEither ProofRelation Γ Δ p q) :=
  inferInstanceAs (Testable (∀ r ∈ Γ, (∃ s ∈ Δ, isSame ProofRelation r s) ∨
    isSame ProofRelation r p ∨ isSame ProofRelation r q))

end Imported.Checker
