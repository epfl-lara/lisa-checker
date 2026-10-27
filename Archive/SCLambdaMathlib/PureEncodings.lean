import Lisa.SCLambdaToPure.PureCalculus

/-! Ordinary rules for the implication/falsity encodings used by Mathlib.
These derived rules let the earlier A/B proofs use the independent target
without changing their connective encodings or their mathematical statements. -/
namespace Lisa.SCLambdaToPure.PureSyntax
open FirstOrder
variable {L : Language.{0, 0}} {mode : Mode} [DecidableEq (Formula L mode)]
variable {T : Theory L mode} {Γ Δ Θ Ξ : Context L mode}

def encodedNot (p : BFormula L mode α n) := p.imp .bot
def encodedAnd (p q : BFormula L mode α n) := encodedNot (p.imp (encodedNot q))
def encodedOr (p q : BFormula L mode α n) := (encodedNot p).imp q
def encodedExists (x : Nat) (p : Formula L mode) := encodedNot (forall_ x (encodedNot p))

namespace ProofTree

def leftEncodedNot (p : Formula L mode) (d : ProofTree T Γ (insert p Δ)) :
    ProofTree T (insert (encodedNot p) Γ) Δ := by
  simpa [encodedNot] using ProofTree.leftImp (Θ := ∅) (Ξ := ∅) p .bot d .leftFalse

def rightEncodedNot (p : Formula L mode) (d : ProofTree T (insert p Γ) Δ) :
    ProofTree T Γ (insert (encodedNot p) Δ) :=
  .rightImp p .bot (d.weakening (by simp) (by simp))

def leftEncodedAnd (p q : Formula L mode) (d : ProofTree T (insert p (insert q Γ)) Δ) :
    ProofTree T (insert (encodedAnd p q) Γ) Δ := by
  apply leftEncodedNot
  apply rightImp
  apply rightEncodedNot
  simpa [Finset.insert_comm] using d

def rightEncodedAnd (p q : Formula L mode)
    (d : ProofTree T Γ (insert p Δ)) (e : ProofTree T Θ (insert q Ξ)) :
    ProofTree T (Γ ∪ Θ) (insert (encodedAnd p q) (Δ ∪ Ξ)) :=
  rightEncodedNot _ (.leftImp p (encodedNot q) d (leftEncodedNot q e))

def leftEncodedOr (p q : Formula L mode)
    (d : ProofTree T (insert p Γ) Δ) (e : ProofTree T (insert q Θ) Ξ) :
    ProofTree T (insert (encodedOr p q) (Γ ∪ Θ)) (Δ ∪ Ξ) :=
  .leftImp (encodedNot p) q (rightEncodedNot p d) e

def rightEncodedOr (p q : Formula L mode) (d : ProofTree T Γ (insert p (insert q Δ))) :
    ProofTree T Γ (insert (encodedOr p q) Δ) :=
  .rightImp (encodedNot p) q (leftEncodedNot p d)

def rightEncodedTrue : ProofTree T ∅ {encodedNot (.bot : Formula L mode)} := by
  simpa using ProofTree.rightImp (Γ := ∅) (Δ := ∅) (.bot : Formula L mode) .bot (.hypothesis .bot)

def leftEncodedExists (x : Nat) (p : Formula L mode) (d : ProofTree T (insert p Γ) Δ)
    (hΓ : Fresh x Γ) (hΔ : Fresh x Δ) : ProofTree T (insert (encodedExists x p) Γ) Δ :=
  leftEncodedNot _ (.rightForall x (encodedNot p) (rightEncodedNot p d) hΓ hΔ)

def rightEncodedExists (x : Nat) (p : Formula L mode) (t : Term L mode)
    (d : ProofTree T Γ (insert (substOne x t p) Δ)) :
    ProofTree T Γ (insert (encodedExists x p) Δ) := by
  apply rightEncodedNot
  apply leftForall x (encodedNot p) t
  exact leftEncodedNot (substOne x t p) d

end ProofTree
end Lisa.SCLambdaToPure.PureSyntax
