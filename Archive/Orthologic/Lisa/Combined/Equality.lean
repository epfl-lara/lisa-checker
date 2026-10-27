import Lisa.Combined.Normalize

namespace Lisa.ExpressionOrder

open Expr

deriving instance Ord for Identifier, LSort, SVar, SConst, Expr

/-- Orient individual equality operands by syntactic order; leave other signatures alone. -/
private def orient : (e : Expr) → ReductionResult e
  | .app (.app (.const c) s) t =>
    if hc : c = SConst.named "eq" (ind >> ind >> prop) then
      if hs : s.sort = some ind then
        if ht : t.sort = some ind then
          if compare s t = .gt then by
            subst c
            exact ⟨eq t s, ⟨.eqSymm s t hs ht, .eqSymm t s ht hs⟩,
              by simp [Expr.eq, Expr.sort, hs, ht], false⟩
          else .unchanged _
        else .unchanged _
      else .unchanged _
    else .unchanged _
  | e => .unchanged e

/-- Orient equalities throughout applications and binders, preserving reference equivalence. -/
def orientEqualities : (e : Expr) → ReductionResult e
  | .app f a =>
    let children := ReductionResult.app (orientEqualities f) (orientEqualities a)
    children.andThen (orient children.expr)
  | .lam x body => ReductionResult.lam x (orientEqualities body)
  | e => .unchanged e

theorem orientEqualities_same (e : Expr) : isSame leq (orientEqualities e).expr e :=
  ⟨(orientEqualities e).same.2, (orientEqualities e).same.1⟩

@[simp] theorem orientEqualities_sort (e : Expr) : (orientEqualities e).expr.sort = e.sort :=
  (orientEqualities e).sort_eq

end Lisa.ExpressionOrder
