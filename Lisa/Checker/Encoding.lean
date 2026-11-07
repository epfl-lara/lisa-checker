import Lisa.Order

namespace Imported.Checker
open Lisa Expr

/-- Compute the sequent formula from its input lists, preserving their order. -/
def listSequentToFormula (pre post : List Expr) : Expr :=
  if pre.isEmpty then foldFormulas or bot post
  else imp (foldFormulas and top pre) (foldFormulas or bot post)

end Imported.Checker
