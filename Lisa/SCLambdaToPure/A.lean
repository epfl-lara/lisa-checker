import Lisa.Lambda.NamedDecision
import Lisa.Sorting
import Lisa.Ordered

/-!
# System A: formulas modulo alpha-beta-eta, without schematic instantiation

This file defines A's expressions, sequents, freshness condition, and inference
rules. Alpha-beta-eta conversion is implicit in formula identity. The calculus
retains generalized simultaneous replacement and epsilon witness selection.

Supporting proofs are in `AToPure/` and `OrderedToA/`. The latter defines B and
eliminates instantiation. The final equivalence theorems are in `Statements.lean`.
-/
namespace Lisa.SCLambdaToPure.A
open Expr

/-- Sorted expressions modulo the already defined αβη relation. -/
abbrev Expression (s : LSort) := {e : AlphaBetaEta.Term // AlphaBetaEta.termSort e = some s}

abbrev Formula := Expression prop
abbrev Term := Expression ind
abbrev Context := Finset Formula

noncomputable instance : DecidableEq Formula := Classical.decEq _

/-- Choose a representative of a sorted conversion class. -/
def ofExpr (e : Expr) (h : e.hasSort s) : Expression s := ⟨AlphaBetaEta.term e, h⟩

/-- A name is fresh if the class admits a representative not using that name.

This is independent of representatives. Beta expansion can introduce unused free
variables, so testing an arbitrary representative's free variables would be wrong.
-/
def Fresh (x : SVar) (Γ : Context) : Prop :=
  ∀ p ∈ Γ, ∃ (e : Expr) (he : isFormula e), ofExpr e he = p ∧ x ∉ e.freeVars

/-- Convert every formula of an existing, sorted Lisa sequent to its class. -/
noncomputable def context (Γ : Finset Expr) (hΓ : isFSet Γ) : Context :=
  Γ.attach.image (fun e : {e // e ∈ Γ} => ofExpr e.val (hΓ e.val e.property))

/-- Only the comparison premise's residual contexts must be fresh for its
pointwise parameters. Freshness is independent of αβη representatives. -/
def RuleFresh (r : SubstRule) (Θ Ξ : Context) : Prop :=
  ∀ c ∈ r.comparisons, ∀ x ∈ c.2, Fresh x Θ ∧ Fresh x Ξ

/-- System A, updated with the generalized replacement and epsilon rules.
Formula identity is αβη equivalence through the quotient defining `Formula`. -/
inductive ProofTree : Context → Context → Type where
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

def Provable (Γ Δ : Context) : Prop := Nonempty (ProofTree Γ Δ)

end Lisa.SCLambdaToPure.A
