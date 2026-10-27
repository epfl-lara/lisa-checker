import Lisa.Checker.Data

namespace Imported.Checker

private def showSort : Lisa.LSort → String
  | .ind => "ι"
  | .prop => "o"
  | .arrow a b => s!"({showSort a}→{showSort b})"

private def showId (id : Lisa.Identifier) : String :=
  if id.idx = 0 then id.name else s!"{id.name}_{id.idx}"

/-- Render all identifiers and sorts without multiline constructor metadata. -/
def showExpr : Lisa.Expr → String
  | .var x => s!"{showId x.id}:{showSort x.sort}"
  | .const c => s!"{showId c.id}:{showSort c.sort}"
  | .app f a => s!"{showExpr f}({showExpr a})"
  | .lam x body => s!"(λ{showId x.id}:{showSort x.sort}. {showExpr body})"

/-- Render a wire sequent for failure diagnostics, not for serialization. -/
def Statement.display (s : Statement) : String :=
  s!"{String.intercalate ", " (s.pre.map showExpr)} ⊢ {String.intercalate ", " (s.post.map showExpr)}"

end Imported.Checker
