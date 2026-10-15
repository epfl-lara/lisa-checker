import Lisa.StandardOrdered
import Lisa.OrderedWeakened
import Tests.OrderModel

open Lisa Expr

namespace AlignmentTests

def x : SVar := ⟨⟨"x", 0⟩, ind⟩
def x1 : SVar := ⟨⟨"x", 1⟩, ind⟩
def x2 : SVar := ⟨⟨"x", 2⟩, ind⟩
def y : SVar := ⟨⟨"y", 0⟩, ind⟩
def p : Expr := .const ⟨⟨"P", 0⟩, ind >> prop⟩
def q : Expr := .app p (.var x1)
def sigma : Subst := .cons y (.var x) .nil

example : freshId {⟨"x", 1⟩, ⟨"y", 99⟩} ⟨"x", 0⟩ = ⟨"x", 2⟩ := by decide
example : freshId ∅ ⟨"x", 10⟩ = ⟨"x", 11⟩ := by decide

-- Freshness must include the body's free variables.
example : sigma.subst (forall_ x q) = forall_ x2 q := by decide
example : x1 ∈ (sigma.subst (forall_ x q)).freeVars := by decide
example : x2 ∉ (sigma.subst (forall_ x q)).freeVars := by decide
example : sigma.subst (forall_ x q) ≠ forall_ x1 q := by decide
example : Subst.subst (.cons y (.var x) (.cons x2 (.var y) .nil))
    (forall_ x q) = forall_ ⟨⟨"x", 3⟩, ind⟩ q := by decide

-- Shadowing removes entries rather than exposing an older replacement.
example : Subst.subst (.cons x (.var y) (.cons x (.var x1) .nil))
    (.lam x (.var x)) = .lam x (.var x) := by decide
example : Subst.subst (.cons x (.var y) .nil) (.lam x (.var x)) =
    .lam x (.var x) := by decide

-- Apply replacements simultaneously, without rewriting their ranges again.
example : Subst.subst (.cons x (.var y) (.cons y (.var x1) .nil)) (.var x) =
    .var y := by decide

def context : SubstContext := ⟨[x], .app p (.var x)⟩
example : context.instantiate [.var x1] = q := by decide
example : context.instantiate [.var x1] ≠ (Expr.lam x (.app p (.var x))).applied [.var x1] :=
  by decide
example : (SubstContext.mk [x, x] (.var x)).instantiate [.var y, .var x1] =
    .var x1 := by decide
example : (SubstContext.mk [] q).instantiate [] = q := by decide
example : ¬ context.fits [] := by unfold SubstContext.fits; decide
example : ¬ context.fits [SubstPair.mk q q] := by unfold SubstContext.fits; decide
example : ¬ (SubstContext.mk [x] (.var x)).wellSorted := by
  simp [SubstContext.wellSorted, x]

def atom : Expr := .const ⟨⟨"A", 0⟩, prop⟩
example : (SubstPair.mk atom atom).liftEq = iff atom atom := by decide
example : (SubstPair.mk atom atom).liftEq.sort = some prop := by decide
example : (SubstPair.mk (.var x) (.var y)).liftEq = eq (.var x) (.var y) := by decide
example : (SubstPair.mk p p).liftEq.sort = some prop := by decide
example : (SubstPair.mk p p).liftEq =
    forall_ x1 (iff (.app p (.var x1)) (.app p (.var x1))) := by decide

-- Quantifier eigenvariables are checked on the whole target sequent.
example : x1 ∈ Lisa.freeVars (({q} : Finset Expr) ∪ {forall_ x1 q}) := by decide

-- Multi-premise connective rules reject an empty premise list.
example : ¬ (([] : List (AnnotatedSequent Expr)) ≠ ∅) := by simp

section Order

variable {leq : Order} [OrderAlgebra leq] [OrderReduction leq]

-- Whole-sequent restatement must identify tautologies with different atoms.
example : sequentLeq leq {atom} {atom} {top} {top} := by
  rw [sequentLeq, OrderAlgebra.compare (leq := leq),
    OrderAlgebra.value_sequent, OrderAlgebra.value_sequent]
  simp only [Finset.inf_singleton, Finset.sup_singleton]
  have h : ∀ a : OrderAlgebra.Carrier (leq := leq), aᶜ ⊔ a = ⊤ :=
    fun a => by rw [sup_comm]; exact Ortholattice.sup_compl a
  simp only [h, le_refl]

-- Instantiation is constrained to the original sides, even for empty substitution.
example : ¬ setLeq leq ({atom} : Finset Expr) ∅ := by
  simp [setLeq]

-- Normalized retained contexts do not silently use the full formula order.
example {r s : Expr} (h : ¬ reducedSame leq r s) :
    ¬ reducedSubset leq {r} {s} := by
  simpa [reducedSubset] using h
example {r s a b : Expr} (h : r ≠ s)
    (ha : ¬ isSame leq r a) (hb : ¬ isSame leq r b) :
    ¬ containedExceptEither leq {r} {s} a b := by
  simpa [containedExceptEither] using And.intro h (And.intro ha hb)

example : Nonempty (Weakened.ProofTree leq ∅ {top}) := by
  apply Nonempty.intro
  apply Weakened.ProofTree.restateTrue
  · simp
  · simp [Expr.top]
  · apply OrderAlgebra.same_iff.mpr
    simp [OrderAlgebra.value_sequent, OrderAlgebra.top_eq, OrderAlgebra.compl_top]

example (h : isSame leq (.var x) (.var y)) :
    Nonempty (Weakened.ProofTree leq ∅ {eq (.var x) (.var y)}) := by
  apply Nonempty.intro
  apply Weakened.ProofTree.rightRefl (.var x) (.var y)
  · simp
  · simp [Expr.eq, x, y]
  · rfl
  · rfl
  · exact h
  · exact ⟨_, Finset.mem_singleton_self _, ⟨OrderAlgebra.reflexive _, OrderAlgebra.reflexive _⟩⟩

example [Nontrivial (OrderAlgebra.Carrier (leq := leq))] :
    ¬ isSame leq (sequentToFormula ∅ {bot}) top := by
  intro h
  have heq := OrderAlgebra.same_iff.mp h
  simp [OrderAlgebra.bot_eq, OrderAlgebra.top_eq, OrderAlgebra.compl_top] at heq

example [Nontrivial (OrderAlgebra.Carrier (leq := leq))] :
    OrderReduction.reduce (leq := leq) top ≠ OrderReduction.reduce (leq := leq) bot := by
  intro h
  have heq := OrderAlgebra.same_iff.mp (OrderReduction.sound top bot h)
  simp [OrderAlgebra.top_eq, OrderAlgebra.bot_eq] at heq

end Order

-- Replay a nonliteral reflexivity step through strict reflexivity and restatement.
def equivalentRefl : Weakened.ProofTree AlignmentModel.leq ∅ {eq (.var x) (.var y)} :=
  Weakened.ProofTree.rightRefl (.var x) (.var y)
    (by simp) (by simp [Expr.eq, x, y]) (by rfl) (by rfl)
    (by unfold isSame AlignmentModel.leq; decide)
    ⟨_, Finset.mem_singleton_self _, ⟨OrderAlgebra.reflexive _, OrderAlgebra.reflexive _⟩⟩

example : (.var x : Expr) ≠ .var y := by decide
example : ¬ isSame AlignmentModel.leq (.var x) (.var x1) := by
  unfold isSame AlignmentModel.leq
  decide
example : Nonempty (Ordered.ProofTree AlignmentModel.leq ∅ {eq (.var x) (.var y)}) :=
  ⟨weakenedToOrdered equivalentRefl⟩

private def hasRightReflReplay {Γ Δ} : Ordered.ProofTree AlignmentModel.leq Γ Δ → Bool
  | .weakening _ _ _ _ (.restate _ _ _ _ (.rightRefl _ _) _ _) _ => true
  | _ => false

example : hasRightReflReplay (weakenedToOrdered equivalentRefl) = true := by rfl

def removedRefl : Weakened.ProofTree AlignmentModel.leq ∅ {top} :=
  Weakened.ProofTree.leftRefl (Γ₁ := {eq (.var x) (.var y)}) (Γ₂ := {top})
    (.var x) (.var y)
    (by simp [Expr.eq, x, y]) (by simp [Expr.top])
    (Weakened.ProofTree.restateTrue
      (by simp [Expr.eq, x, y]) (by simp [Expr.top])
      (by
        apply OrderAlgebra.same_iff.mpr
        simp [OrderAlgebra.top_eq]))
    (by simp) (by simp [Expr.top]) (by rfl) (by rfl)
    (by unfold isSame AlignmentModel.leq; decide)
    (reducedSubset_of_subset (Finset.Subset.refl _))
    (by
      intro p hp
      have h := Finset.mem_singleton.mp hp
      subst p
      exact Or.inr ⟨OrderAlgebra.reflexive _, OrderAlgebra.reflexive _⟩)

example : Nonempty (Ordered.ProofTree AlignmentModel.leq ∅ {top}) :=
  ⟨weakenedToOrdered removedRefl⟩

private def hasLeftReflReplay {Γ Δ} : Ordered.ProofTree AlignmentModel.leq Γ Δ → Bool
  | .leftRefl _ _ _ _ (.restate _ _ _ _ _ _ _) => true
  | _ => false

example : hasLeftReflReplay (weakenedToOrdered removedRefl) = true := by rfl

#print axioms ordered_eq_weakened
#print axioms StandardOrdered.standard_eq_ordered
#print axioms Subst.subst_preserves_sort
#print axioms freshId_not_mem
#print axioms OrderAlgebra.sequentLeq_of_setLeq
#print axioms OrderReduction.sound
#print axioms equivalentRefl
#print axioms removedRefl

end AlignmentTests
