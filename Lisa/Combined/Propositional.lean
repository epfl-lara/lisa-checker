import Lisa.Order
import Lisa.Orthologic.Normalize

namespace Lisa.Orthologic

open Expr

/-- Reify exact logical constants; retain other expressions as opaque atoms. -/
def reify : Expr → Formula Expr
  | .const c =>
      if c = SConst.named "top" prop then .top
      else if c = SConst.named "bot" prop then .bot
      else .atom (.const c)
  | .app (.const c) p =>
      if c = SConst.named "not" (prop >> prop) then .neg (reify p)
      else .atom (.app (.const c) p)
  | .app (.app (.const c) p) q =>
      if c = SConst.named "and" (prop >> prop >> prop) then .meet (reify p) (reify q)
      else if c = SConst.named "or" (prop >> prop >> prop) then .join (reify p) (reify q)
      else if c = SConst.named "imp" (prop >> prop >> prop) then
        .join (.neg (reify p)) (reify q)
      else if c = SConst.named "iff" (prop >> prop >> prop) then
        .meet (.join (.neg (reify p)) (reify q)) (.join (.neg (reify q)) (reify p))
      else .atom (.app (.app (.const c) p) q)
  | p => .atom p

/-- Preserve the interpretation supplied by any expression-order algebra. -/
@[simp] theorem eval_reify {leq : Order} [OrderAlgebra leq] (p : Expr) :
    (reify p).eval (OrderAlgebra.eval (leq := leq)) = OrderAlgebra.eval p := by
  fun_induction reify
  all_goals simp_all only [Formula.eval]
  all_goals first
    | rfl
    | exact OrderAlgebra.top_eq.symm
    | exact OrderAlgebra.bot_eq.symm
    | exact (OrderAlgebra.neg_eq _).symm
    | exact (OrderAlgebra.and_eq _ _).symm
    | exact (OrderAlgebra.or_eq _ _).symm
    | exact (OrderAlgebra.imp_eq _ _).symm
    | exact (OrderAlgebra.iff_eq _ _).symm

/-- Reconstruct logical syntax without changing opaque atoms. -/
def Formula.toExpr : Formula Expr → Expr
  | .atom p => p
  | .bot => Expr.bot
  | .top => Expr.top
  | .meet p q => and p.toExpr q.toExpr
  | .join p q => or p.toExpr q.toExpr
  | .neg p => Expr.neg p.toExpr

@[simp] theorem Formula.eval_toExpr {leq : Order} [OrderAlgebra leq]
    (p : Formula Expr) : OrderAlgebra.eval (leq := leq) p.toExpr =
      p.eval OrderAlgebra.eval := by
  induction p <;> simp_all [Formula.toExpr, Formula.eval,
    OrderAlgebra.top_eq, OrderAlgebra.bot_eq, OrderAlgebra.and_eq,
    OrderAlgebra.or_eq, OrderAlgebra.neg_eq]

/-- Normalize propositional structure while leaving binders and terms opaque. -/
def normalizeExpr (p : Expr) : Expr := (reify p).normalize.toFormula.toExpr

@[simp] theorem eval_normalizeExpr {leq : Order} [OrderAlgebra leq] (p : Expr) :
    OrderAlgebra.eval (leq := leq) (normalizeExpr p) = OrderAlgebra.eval p := by
  simp [normalizeExpr]

/-- Preserve sort even for malformed or non-propositional expressions. -/
def reduceExpr (p : Expr) : Expr :=
  let result := normalizeExpr p
  if result.sort = p.sort then result else p

@[simp] theorem sort_reduceExpr (p : Expr) : (reduceExpr p).sort = p.sort := by
  dsimp only [reduceExpr]
  split <;> simp_all

theorem same_reduceExpr {leq : Order} [OrderAlgebra leq] (p : Expr) :
    isSame leq (reduceExpr p) p := by
  apply OrderAlgebra.same_iff.mpr
  dsimp only [reduceExpr]
  split <;> simp

/-- Supply the verified propositional reducer without installing a global instance. -/
@[reducible] def reduction (leq : Order) [OrderAlgebra leq] : OrderReduction leq where
  reduce := reduceExpr
  preserves := same_reduceExpr
  preservesSort := sort_reduceExpr

/-- Certify successful comparisons; do not interpret failure as inequivalence. -/
def checkExprLe (p q : Expr) : Bool :=
  Nnf.checkNormalizedLe (reify p).toNnf (reify q).toNnf

theorem checkExprLe_sound {leq : Order} [OrderAlgebra leq] (p q : Expr)
    (h : checkExprLe p q = true) : leq p q := by
  apply (OrderAlgebra.compare p q).mpr
  simpa using Nnf.checkNormalizedLe_sound (OrderAlgebra.eval (leq := leq)) h

/-- Return an erased order certificate when normalized containment succeeds. -/
def proveLe {leq : Order} [OrderAlgebra leq] (p q : Expr) : Option (PLift (leq p q)) :=
  if h : checkExprLe p q = true then some ⟨checkExprLe_sound p q h⟩ else none

end Lisa.Orthologic
