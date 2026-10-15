import Lisa.Combined.ContextualProjection
import Lisa.Combined.Reference

namespace Lisa.Orthologic.ContextualReflection

open Expr Contextual

/-- Distinguish application from each named binder; impose no constructor monotonicity. -/
inductive Constructor where
  | app
  | lam (x : SVar)
  deriving DecidableEq, Repr

/-- Reify logical constants even when they occur inside applications or binders. -/
def reify : Expr → Term Expr Constructor
  | .var x => .atom (.var x)
  | .const c =>
      if c = SConst.named "top" prop then .top
      else if c = SConst.named "bot" prop then .bot
      else .atom (.const c)
  | .app (.const c) p =>
      if c = SConst.named "not" (prop >> prop) then .neg (reify p)
      else .binary .app (reify (.const c)) (reify p)
  | .app (.app (.const c) p) q =>
      if c = SConst.named "and" (prop >> prop >> prop) then .meet (reify p) (reify q)
      else if c = SConst.named "or" (prop >> prop >> prop) then .join (reify p) (reify q)
      else if c = SConst.named "imp" (prop >> prop >> prop) then
        .join (.neg (reify p)) (reify q)
      else if c = SConst.named "iff" (prop >> prop >> prop) then
        .meet (.join (.neg (reify p)) (reify q)) (.join (.neg (reify q)) (reify p))
      else .binary .app (.binary .app (reify (.const c)) (reify p)) (reify q)
  | .app f a => .binary .app (reify f) (reify a)
  | .lam x b => .unary (.lam x) (reify b)

/-- Interpret an expression in the contextual term model. -/
def value (p : Expr) : TheoryModel Expr Constructor := Contextual.value (reify p)

/-- Interpret the propositional shell in the contextual term model. -/
@[reducible] def algebra : OrderAlgebra (fun p q => value p ≤ value q) where
  Carrier := TheoryModel Expr Constructor
  algebra := inferInstance
  eval := value
  compare := fun _ _ => Iff.rfl
  top_eq := rfl
  bot_eq := rfl
  and_eq := fun _ _ => rfl
  or_eq := fun _ _ => rfl
  neg_eq := fun _ => rfl
  imp_eq := fun _ _ => rfl
  iff_eq := fun _ _ => rfl

/-- Interpret binder congruence in the reference quotient. -/
def unary : Constructor → ExpressionOrder.Carrier → ExpressionOrder.Carrier
  | .app => id
  | .lam x => Quotient.lift (fun p => ExpressionOrder.value (.lam x p))
      (fun _ _ h => Quotient.sound (ExpressionOrder.same_lam x h))

/-- Interpret application congruence in the reference quotient. -/
def binary (_ : Constructor) :
    ExpressionOrder.Carrier → ExpressionOrder.Carrier → ExpressionOrder.Carrier :=
  Quotient.lift₂ (fun f a => ExpressionOrder.value (.app f a))
    (fun _ _ _ _ hf ha => Quotient.sound (ExpressionOrder.same_app hf ha))

@[simp] theorem unary_value (x : SVar) (p : Expr) :
    unary (.lam x) (ExpressionOrder.value p) = ExpressionOrder.value (.lam x p) := rfl

@[simp] theorem binary_value (k : Constructor) (f a : Expr) :
    binary k (ExpressionOrder.value f) (ExpressionOrder.value a) =
      ExpressionOrder.value (.app f a) := rfl

/-- Preserve reference interpretation through every reified constructor. -/
@[simp] theorem eval_reify (p : Expr) :
    (reify p).eval ExpressionOrder.value unary binary = ExpressionOrder.value p := by
  fun_induction reify
  all_goals simp_all only [Term.eval, unary_value, binary_value]
  all_goals first
    | rfl
    | exact (OrderAlgebra.top_eq (leq := ExpressionOrder.leq)).symm
    | exact (OrderAlgebra.bot_eq (leq := ExpressionOrder.leq)).symm
    | exact (OrderAlgebra.neg_eq (leq := ExpressionOrder.leq) _).symm
    | exact (OrderAlgebra.and_eq (leq := ExpressionOrder.leq) _ _).symm
    | exact (OrderAlgebra.or_eq (leq := ExpressionOrder.leq) _ _).symm
    | exact (OrderAlgebra.imp_eq (leq := ExpressionOrder.leq) _ _).symm
    | exact (OrderAlgebra.iff_eq (leq := ExpressionOrder.leq) _ _).symm

end Lisa.Orthologic.ContextualReflection
