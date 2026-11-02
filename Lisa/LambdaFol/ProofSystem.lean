import Lisa.LambdaFol.EliminateInstantiation.Instantiation

/-! LambdaFOL on formulas modulo αβη, including schematic instantiation,
generalized simultaneous replacement, and epsilon. -/
namespace Lisa.LambdaFol
open Expr

inductive ProofTree : Finset Formula → Finset Formula → Type where
  | hypothesis (p : Formula) : ProofTree {p} {p}
  | weakening {Γ Δ Γ' Δ'} :
      ProofTree Γ Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → ProofTree Γ' Δ'
  | cut {Γ Δ Γ₁ Δ₁} (p : Formula) :
      ProofTree Γ (insert p Δ) → ProofTree (insert p Γ₁) Δ₁ →
      ProofTree (Γ ∪ Γ₁) (Δ ∪ Δ₁)
  | leftFalse : ProofTree {ofExpr (s := prop) bot rfl} ∅
  | rightTrue : ProofTree ∅ {ofExpr (s := prop) top rfl}
  | leftAnd {Γ Δ} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree (insert (ofExpr p hp) (insert (ofExpr q hq) Γ)) Δ →
      ProofTree (insert (ofExpr (and p q) (isFormula_and hp hq)) Γ) Δ
  | rightAnd {Γ Δ Γ₁ Δ₁} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree Γ (insert (ofExpr p hp) Δ) →
      ProofTree Γ₁ (insert (ofExpr q hq) Δ₁) →
      ProofTree (Γ ∪ Γ₁) (insert (ofExpr (and p q) (isFormula_and hp hq)) (Δ ∪ Δ₁))
  | leftOr {Γ Δ Γ₁ Δ₁} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree (insert (ofExpr p hp) Γ) Δ →
      ProofTree (insert (ofExpr q hq) Γ₁) Δ₁ →
      ProofTree (insert (ofExpr (or p q) (isFormula_or hp hq)) (Γ ∪ Γ₁)) (Δ ∪ Δ₁)
  | rightOr {Γ Δ} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree Γ (insert (ofExpr p hp) (insert (ofExpr q hq) Δ)) →
      ProofTree Γ (insert (ofExpr (or p q) (isFormula_or hp hq)) Δ)
  | leftImp {Γ Δ Γ₁ Δ₁} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree Γ (insert (ofExpr p hp) Δ) →
      ProofTree (insert (ofExpr q hq) Γ₁) Δ₁ →
      ProofTree (insert (ofExpr (imp p q) (isFormula_imp hp hq)) (Γ ∪ Γ₁)) (Δ ∪ Δ₁)
  | rightImp {Γ Δ} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree (insert (ofExpr p hp) Γ) (insert (ofExpr q hq) Δ) →
      ProofTree Γ (insert (ofExpr (imp p q) (isFormula_imp hp hq)) Δ)
  | leftIff {Γ Δ} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree (insert (ofExpr (imp p q) (isFormula_imp hp hq))
        (insert (ofExpr (imp q p) (isFormula_imp hq hp)) Γ)) Δ →
      ProofTree (insert (ofExpr (iff p q) (isFormula_iff hp hq)) Γ) Δ
  | rightIff {Γ Δ Γ₁ Δ₁} (p q : Expr) (hp : isFormula p) (hq : isFormula q) :
      ProofTree Γ (insert (ofExpr (imp p q) (isFormula_imp hp hq)) Δ) →
      ProofTree Γ₁ (insert (ofExpr (imp q p) (isFormula_imp hq hp)) Δ₁) →
      ProofTree (Γ ∪ Γ₁) (insert (ofExpr (iff p q) (isFormula_iff hp hq)) (Δ ∪ Δ₁))
  | leftNot {Γ Δ} (p : Expr) (hp : isFormula p) :
      ProofTree Γ (insert (ofExpr p hp) Δ) →
      ProofTree (insert (ofExpr (neg p) (isFormula_neg hp)) Γ) Δ
  | rightNot {Γ Δ} (p : Expr) (hp : isFormula p) :
      ProofTree (insert (ofExpr p hp) Γ) Δ →
      ProofTree Γ (insert (ofExpr (neg p) (isFormula_neg hp)) Δ)
  | leftForall {Γ Δ} (x : SVar) (p t : Expr)
      (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) :
      ProofTree (insert (ofExpr (substOne x t p) (isFormula_substOne hx ht hp)) Γ) Δ →
      ProofTree (insert (ofExpr (forall_ x p) (isFormula_forall hx hp)) Γ) Δ
  | rightForall {Γ Δ} (x : SVar) (p : Expr) (hx : x.sort = ind) (hp : isFormula p) :
      ProofTree Γ (insert (ofExpr p hp) Δ) → Fresh x Γ → Fresh x Δ →
      ProofTree Γ (insert (ofExpr (forall_ x p) (isFormula_forall hx hp)) Δ)
  | leftExists {Γ Δ} (x : SVar) (p : Expr) (hx : x.sort = ind) (hp : isFormula p) :
      ProofTree (insert (ofExpr p hp) Γ) Δ → Fresh x Γ → Fresh x Δ →
      ProofTree (insert (ofExpr (exists_ x p) (isFormula_exists hx hp)) Γ) Δ
  | rightExists {Γ Δ} (x : SVar) (p t : Expr)
      (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) :
      ProofTree Γ (insert (ofExpr (substOne x t p) (isFormula_substOne hx ht hp)) Δ) →
      ProofTree Γ (insert (ofExpr (exists_ x p) (isFormula_exists hx hp)) Δ)
  | refl (t : Expr) (ht : isTerm t) :
      ProofTree ∅ {ofExpr (eq t t) (isFormula_eq ht ht)}
  | rightEpsilon {Γ Δ} (x : SVar) (p t : Expr)
      (hx : x.sort = ind) (hp : isFormula p) (ht : isTerm t) :
      ProofTree Γ (insert (ofExpr (substOne x t p) (isFormula_substOne hx ht hp)) Δ) →
      ProofTree Γ (insert (ofExpr (substOne x (epsilon_ (.lam x p)) p)
        (isFormula_substOne hx (isTerm_epsilon hx hp) hp)) Δ)
  | leftReplace {Γ Δ Θ Ξ} (r : SubstRule) (hr : r.valid) (hf : RuleFresh r Θ Ξ) :
      ProofTree (insert (ofExpr r.source hr.2.2.2.1) Γ) Δ →
      ProofTree Θ (insert (ofExpr r.equation (SubstRule.equation_isFormula hr)) Ξ) →
      ProofTree (insert (ofExpr r.target hr.2.2.2.2) (Γ ∪ Θ)) (Δ ∪ Ξ)
  | rightReplace {Γ Δ Θ Ξ} (r : SubstRule) (hr : r.valid) (hf : RuleFresh r Θ Ξ) :
      ProofTree Γ (insert (ofExpr r.source hr.2.2.2.1) Δ) →
      ProofTree Θ (insert (ofExpr r.equation (SubstRule.equation_isFormula hr)) Ξ) →
      ProofTree (Γ ∪ Θ) (insert (ofExpr r.target hr.2.2.2.2) (Δ ∪ Ξ))
  | instSchema {Γ Δ} (σ : Instantiation) :
      ProofTree Γ Δ → ProofTree (σ.formulaSet Γ) (σ.formulaSet Δ)

def Provable (Γ Δ : Finset LambdaFol.Formula) : Prop := Nonempty (ProofTree Γ Δ)

end Lisa.LambdaFol
