import Lisa.Orthologic.ExpressionModel
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
@[simp] theorem eval_reify {leq : ExprRel} (m : Interpretation leq) (p : Expr) :
    (reify p).eval (m.eval) = m.eval p := by
  fun_induction reify
  all_goals simp_all only [Formula.eval]
  all_goals first
    | rfl
    | exact m.top_eq.symm
    | exact m.bot_eq.symm
    | exact (m.neg_eq _).symm
    | exact (m.and_eq _ _).symm
    | exact (m.or_eq _ _).symm
    | exact (m.imp_eq _ _).symm
    | exact (m.iff_eq _ _).symm

/-- Reconstruct logical syntax without changing opaque atoms. -/
def Formula.toExpr : Formula Expr → Expr
  | .atom p => p
  | .bot => Expr.bot
  | .top => Expr.top
  | .meet p q => and p.toExpr q.toExpr
  | .join p q => or p.toExpr q.toExpr
  | .neg p => Expr.neg p.toExpr

@[simp] theorem Formula.eval_toExpr {leq : ExprRel} (m : Interpretation leq)
    (p : Formula Expr) : m.eval p.toExpr =
      p.eval m.eval := by
  induction p <;> simp_all [Formula.toExpr, Formula.eval,
    m.top_eq, m.bot_eq, m.and_eq,
    m.or_eq, m.neg_eq]

/-- Normalize propositional structure while leaving binders and terms opaque. -/
def normalizeExpr (p : Expr) : Expr := (reify p).normalize.toFormula.toExpr

@[simp] theorem eval_normalizeExpr {leq : ExprRel} (m : Interpretation leq) (p : Expr) :
    m.eval (normalizeExpr p) = m.eval p := by
  simp [normalizeExpr, Formula.eval_toExpr m, eval_reify m]

theorem same_normalizeExpr {leq : ExprRel} (m : Interpretation leq) (p : Expr) :
    isSame leq (normalizeExpr p) p := m.same_iff.mpr (eval_normalizeExpr m p)

/-- Preserve sort even for malformed or non-propositional expressions. -/
def reduceExpr (p : Expr) : Expr :=
  let result := normalizeExpr p
  if result.sort = p.sort then result else p

@[simp] theorem sort_reduceExpr (p : Expr) : (reduceExpr p).sort = p.sort := by
  dsimp only [reduceExpr]
  split <;> simp_all

theorem same_reduceExpr {leq : ExprRel} (m : Interpretation leq) (p : Expr) :
    isSame leq (reduceExpr p) p := by
  dsimp only [reduceExpr]
  split
  · exact same_normalizeExpr m p
  · exact m.same_refl p

/-- Supply the verified propositional reducer without installing a global instance. -/
@[reducible] def reduction (leq : ExprRel) (m : Interpretation leq) : OrderReduction leq :=
  letI := m.preorder
  OrderReduction.of reduceExpr (same_reduceExpr m) sort_reduceExpr

/-- Certify successful comparisons; do not interpret failure as inequivalence. -/
def checkExprLe (p q : Expr) : Bool :=
  Nnf.checkNormalizedLe (reify p).toNnf (reify q).toNnf

theorem checkExprLe_sound {leq : ExprRel} (m : Interpretation leq) (p q : Expr)
    (h : checkExprLe p q = true) : leq p q := by
  apply (m.compare p q).mpr
  have result := Nnf.checkNormalizedLe_sound m.eval h
  simpa only [Formula.eval_toNnf, eval_reify m] using result

/-- Return an erased order certificate when normalized containment succeeds. -/
def proveLe {leq : ExprRel} (m : Interpretation leq) (p q : Expr) : Option (PLift (leq p q)) :=
  if h : checkExprLe p q = true then some ⟨checkExprLe_sound m p q h⟩ else none

end Lisa.Orthologic
