import Lisa.SCLambdaToPure.CanonicalReduction

/-! Relate the two presentations of first-order connectives by derivations.
In particular, an encoded conjunction is not an αβη-equal conjunction. -/

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder

structure Related (η : Nat → Identifier) (p : A.Formula)
    (q : Pure.Formula Readback.language) where
  forward : A.ProofTree ∅ {p} {ofFormula η q}
  backward : A.ProofTree ∅ {ofFormula η q} {p}

namespace Related

variable {η : Nat → Identifier} {p q : Expr} {hp : isFormula p} {hq : isFormula q}
  {p' q' : Pure.Formula Readback.language}

def of_eq {p : A.Formula} {q : Pure.Formula Readback.language} (h : p = ofFormula η q) :
    Related η p q := by
  subst p
  exact ⟨.hypothesis _, .hypothesis _⟩

def bot : Related η (A.ofExpr Expr.bot rfl) ⊥ := of_eq rfl

noncomputable def top : Related η (A.ofExpr Expr.top rfl) ⊤ := ⟨
  .weakening (rightTop (η := η)) (by simp) (by simp),
  .weakening .rightTrue (by simp) (by simp)⟩

noncomputable def neg (h : Related η (A.ofExpr p hp) p') :
    Related η (A.ofExpr (Expr.neg p) (isFormula_neg hp)) p'.not := by
  constructor
  · apply rightNot (Δ := ∅) p'
    simpa [Finset.pair_comm] using A.ProofTree.leftNot (Γ := {ofFormula η p'}) (Δ := ∅) p hp
      (by simpa using h.backward)
  · apply A.ProofTree.rightNot (Δ := ∅) p hp
    simpa [Finset.pair_comm] using leftNot (Γ := {A.ofExpr p hp}) (Δ := ∅) p'
      (by simpa using h.forward)

noncomputable def and (h : Related η (A.ofExpr p hp) p')
    (k : Related η (A.ofExpr q hq) q') :
    Related η (A.ofExpr (Expr.and p q) (isFormula_and hp hq)) (p' ⊓ q') := by
  constructor
  · apply A.ProofTree.leftAnd (Γ := ∅)
    simpa using rightAnd (Γ := {A.ofExpr p hp}) (Γ' := {A.ofExpr q hq}) (Δ := ∅) (Δ' := ∅)
      p' q' (by simpa using h.forward) (by simpa using k.forward)
  · apply leftAnd (Γ := ∅)
    simpa using A.ProofTree.rightAnd (Γ := {ofFormula η p'}) (Γ₁ := {ofFormula η q'})
      (Δ := ∅) (Δ₁ := ∅) p q hp hq (by simpa using h.backward) (by simpa using k.backward)

noncomputable def or (h : Related η (A.ofExpr p hp) p')
    (k : Related η (A.ofExpr q hq) q') :
    Related η (A.ofExpr (Expr.or p q) (isFormula_or hp hq)) (p' ⊔ q') := by
  constructor
  · apply rightOr (Δ := ∅)
    simpa using A.ProofTree.leftOr (Γ := ∅) (Γ₁ := ∅)
      (Δ := {ofFormula η p'}) (Δ₁ := {ofFormula η q'}) p q hp hq
      (by simpa using h.forward) (by simpa using k.forward)
  · apply A.ProofTree.rightOr (Δ := ∅)
    simpa using leftOr (Γ := ∅) (Γ' := ∅) (Δ := {A.ofExpr p hp}) (Δ' := {A.ofExpr q hq})
      p' q' (by simpa using h.backward) (by simpa using k.backward)

noncomputable def imp (h : Related η (A.ofExpr p hp) p')
    (k : Related η (A.ofExpr q hq) q') :
    Related η (A.ofExpr (Expr.imp p q) (isFormula_imp hp hq)) (p'.imp q') := by
  constructor
  · apply rightImp (Δ := ∅) p' q'
    simpa [Finset.insert_comm, Finset.pair_comm] using A.ProofTree.leftImp
      (Γ := {ofFormula η p'}) (Γ₁ := ∅) (Δ := ∅) (Δ₁ := {ofFormula η q'})
      p q hp hq (by simpa using h.backward) (by simpa using k.forward)
  · apply A.ProofTree.rightImp (Δ := ∅) p q hp hq
    simpa [Finset.insert_comm, Finset.pair_comm] using leftImp
      (Γ := {A.ofExpr p hp}) (Γ' := ∅) (Δ := ∅) (Δ' := {A.ofExpr q hq})
      p' q' (by simpa using h.forward) (by simpa using k.backward)

noncomputable def iff (h : Related η (A.ofExpr p hp) p')
    (k : Related η (A.ofExpr q hq) q') :
    Related η (A.ofExpr (Expr.iff p q) (isFormula_iff hp hq)) (p'.iff q') := by
  let hpq := h.imp k
  let hqp := k.imp h
  constructor
  · apply A.ProofTree.leftIff (Γ := ∅) p q hp hq
    simpa using rightAnd (Γ := {A.ofExpr (Expr.imp p q) (isFormula_imp hp hq)})
      (Γ' := {A.ofExpr (Expr.imp q p) (isFormula_imp hq hp)}) (Δ := ∅) (Δ' := ∅)
      (p'.imp q') (q'.imp p') (by simpa using hpq.forward) (by simpa using hqp.forward)
  · apply leftAnd (Γ := ∅)
    simpa using A.ProofTree.rightIff (Γ := {ofFormula η (p'.imp q')})
      (Γ₁ := {ofFormula η (q'.imp p')}) (Δ := ∅) (Δ₁ := ∅) p q hp hq
      (by simpa using hpq.backward) (by simpa using hqp.backward)

end Related
end Lisa.SCLambdaToPure.Embedding

