import Lisa.AlphaBetaEtaNormalization.NamedDecision
import Lisa.Sorting
import Lisa.Ordered

/-! Sorted expressions modulo αβη, formula sets, and freshness shared by
the LambdaFOL proof systems. -/
namespace Lisa.LambdaFol
open Expr

/-- Expressions of sort `s`, modulo αβη equivalence. -/
abbrev Expression (s : LSort) := {e : AlphaBetaEta.Term // AlphaBetaEta.termSort e = some s}

abbrev Formula := Expression prop
abbrev Term := Expression ind

noncomputable instance : DecidableEq Formula := Classical.decEq _

/-- Form the αβη class of a sorted expression. -/
def ofExpr (e : Expr) (h : e.hasSort s) : Expression s := ⟨AlphaBetaEta.term e, h⟩

/-- A name is fresh if the class admits a representative not using that name.

This is independent of representatives. Beta expansion can introduce unused free
variables, so testing an arbitrary representative's free variables would be wrong.
-/
def Fresh (x : SVar) (Γ : Finset Formula) : Prop :=
  ∀ p ∈ Γ, ∃ (e : Expr) (he : isFormula e), ofExpr e he = p ∧ x ∉ e.freeVars

/-- Map a set of well-sorted formulas to their αβη classes. -/
noncomputable def formulaSet (Γ : Finset Expr) (hΓ : isFSet Γ) : Finset Formula :=
  Γ.attach.image (fun e : {e // e ∈ Γ} => ofExpr e.val (hΓ e.val e.property))

/-- Only the comparison premise's residual formula sets must be fresh for its
pointwise parameters. Freshness is independent of αβη representatives. -/
def RuleFresh (r : SubstRule) (Θ Ξ : Finset Formula) : Prop :=
  ∀ c ∈ r.comparisons, ∀ x ∈ c.2, Fresh x Θ ∧ Fresh x Ξ


end Lisa.LambdaFol
