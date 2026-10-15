import Lisa.Combined.Reference
import Lisa.Combined.Propositional

/-! Reduce expression contexts with erased order-equivalence and sort certificates. -/

namespace Lisa.ExpressionOrder

open Expr

/-- Retain the normalized syntax and erase its equivalence and sort certificates. -/
structure ReductionResult (input : Expr) where
  expr : Expr
  same : isSame leq input expr
  sort_eq : expr.sort = input.sort
  /-- Record whether a recursive call reached zero fuel, even if its input was already normal. -/
  exhausted : Bool := false

namespace ReductionResult

def unchanged (e : Expr) (exhausted := false) : ReductionResult e :=
  ⟨e, ⟨.refl e, .refl e⟩, rfl, exhausted⟩

def converted {p q : Expr} (h : Conversion p q) : ReductionResult p :=
  ⟨q, same_of_conversion h, h.preserves_sort.symm, false⟩

def andThen {e : Expr} (first : ReductionResult e) (next : ReductionResult first.expr) :
    ReductionResult e :=
  ⟨next.expr, ⟨.trans first.same.1 next.same.1, .trans next.same.2 first.same.2⟩,
    next.sort_eq.trans first.sort_eq, first.exhausted || next.exhausted⟩

def app {f a : Expr} (rf : ReductionResult f) (ra : ReductionResult a) :
    ReductionResult (.app f a) :=
  ⟨.app rf.expr ra.expr, same_app rf.same ra.same,
    by simp only [Expr.sort, rf.sort_eq, ra.sort_eq], rf.exhausted || ra.exhausted⟩

def lam (x : SVar) {p : Expr} (rp : ReductionResult p) : ReductionResult (.lam x p) :=
  ⟨.lam x rp.expr, same_lam x rp.same,
    by simp only [Expr.sort, rp.sort_eq], rp.exhausted⟩

end ReductionResult

/-- Simplify propositional structure without changing sort or order equivalence. -/
private def lattice (e : Expr) : ReductionResult e :=
  ⟨Orthologic.reduceExpr e,
    let h := Orthologic.same_reduceExpr (leq := leq) e
    ⟨h.2, h.1⟩,
    Orthologic.sort_reduceExpr e, false⟩

/-- Contract eta only after normalizing the abstraction body. -/
private def eta : (e : Expr) → ReductionResult e
  | .lam x (.app f (.var y)) =>
    if hxy : y = x then
      match hf : f.sort with
      | some (.arrow domain range) =>
        if hd : domain = x.sort then
          if hfree : x ∉ f.freeVars then
            .converted (by
              subst y
              exact Conversion.eta x f range (by simpa [hd] using hf) hfree)
          else .unchanged _
        else .unchanged _
      | _ => .unchanged _
    else .unchanged _
  | e => .unchanged e

/-- Choose a variable outside the expression's free variables. -/
def freshVariable (e : Expr) (s : LSort) : SVar :=
  ⟨freshId (e.freeVars.image (·.id)) ⟨"bound", 0⟩, s⟩

theorem freshVariable_not_mem (e : Expr) (s : LSort) :
    freshVariable e s ∉ e.freeVars := by
  intro h
  apply freshId_not_mem (e.freeVars.image (fun v => v.id)) ⟨"bound", 0⟩
  exact Finset.mem_image.mpr ⟨freshVariable e s, h, rfl⟩

/-- Expand an existential predicate using a fresh individual variable. -/
private def existential (p : Expr) (hp : p.sort = some (ind >> prop)) :
    ReductionResult (.app (.const (.named "exists" ((ind >> prop) >> prop))) p) := by
  let x := freshVariable p ind
  have hx : x.sort = ind := rfl
  have hbody : isFormula (.app p (.var x)) := by simp [isFormula, Expr.hasSort, Expr.sort, hp, hx]
  have he := same_of_conversion (Conversion.app (.refl (.const
    (.named "exists" ((ind >> prop) >> prop))))
    (Conversion.eta x p prop hp (freshVariable_not_mem p ind)).symm)
  refine ⟨neg (forall_ x (neg (.app p (.var x)))),
    ⟨.trans he.1 (.exists x _ hx hbody),
      .trans (.existsRev x _ hx hbody) he.2⟩, ?_, false⟩
  simp [Expr.neg, Expr.forall_, Expr.sort, hp, hx]

/-- Simplify equality and quantified bounds, and unfold existential predicates. -/
private def builtin : (e : Expr) → ReductionResult e
  | .app (.app (.const c) s) t =>
    if hc : c = SConst.named "eq" (ind >> ind >> prop) then
      if hs : s.sort = some ind then
        if ht : t.sort = some ind then
          if he : AlphaEq s t then by
            subst c
            have hterm := same_of_conversion (Conversion.alpha he)
            have heq := TermEqualityCongruence.refl_eq hs ht hterm
            exact ⟨top, ⟨.top _, .trans (.eqRefl s hs) heq.1⟩,
              by simp [Expr.top, Expr.sort, hs, ht], false⟩
          else .unchanged _
        else .unchanged _
      else .unchanged _
    else .unchanged _
  | .app (.const c) p =>
    if hc : c = SConst.named "exists" ((ind >> prop) >> prop) then
      if hp : p.sort = some (ind >> prop) then by
        subst c
        exact existential p hp
      else .unchanged _
    else if hc : c = SConst.named "forall" ((ind >> prop) >> prop) then
      match p with
      | .lam x body =>
        if hx : x.sort = ind then
          if hb : body = top then by
            subst c body
            exact ⟨top, ⟨.top _, .forallTop x hx⟩,
              by simp [Expr.top, Expr.sort, hx], false⟩
          else if hb : body = bot then by
            subst c body
            exact ⟨bot, ⟨.forallBot x hx, .bot _⟩,
              by simp [Expr.bot, Expr.sort, hx], false⟩
          else .unchanged _
        else .unchanged _
      | _ => .unchanged _
    else .unchanged _
  | e => .unchanged e

/-- Simplify builtin constants at every depth without running OL search. -/
def simplifyBuiltins : (e : Expr) → ReductionResult e
  | .app f a =>
      let children := ReductionResult.app (simplifyBuiltins f) (simplifyBuiltins a)
      children.andThen (builtin children.expr)
  | .lam x body => ReductionResult.lam x (simplifyBuiltins body)
  | e => builtin e

/-- Normalize beta, eta, and OL structure throughout an expression.

Recurse under binders and applications; normalize newly exposed beta results.
Use fuel rather than assuming normalization or completeness of the term calculus.
An exhausted result remains certified equivalent to its input.
-/
def normalize : Nat → (e : Expr) → ReductionResult e
  | 0, e => .unchanged e true
  | fuel + 1, e =>
    let children : ReductionResult e := match e with
      | .app f a => .app (normalize fuel f) (normalize fuel a)
      | .lam x body => .lam x (normalize fuel body)
      | _ => .unchanged _
    let contracted : ReductionResult children.expr := match children.expr with
      | .app (.lam x body) arg =>
        if ha : arg.sort = some x.sort then
          let beta := ReductionResult.converted (Conversion.beta x body arg ha)
          beta.andThen (normalize fuel beta.expr)
        else .unchanged _
      | e => .unchanged e
    let simplified := lattice contracted.expr
    let unfolded := builtin simplified.expr
    let finished := if unfolded.expr = simplified.expr then unfolded
      else unfolded.andThen (normalize fuel unfolded.expr)
    children.andThen (contracted.andThen (simplified.andThen
      (finished.andThen (eta finished.expr))))

@[simp] theorem normalize_sort (fuel : Nat) (e : Expr) :
    (normalize fuel e).expr.sort = e.sort := (normalize fuel e).sort_eq

theorem normalize_same (fuel : Nat) (e : Expr) :
    isSame leq (normalize fuel e).expr e :=
  ⟨(normalize fuel e).same.2, (normalize fuel e).same.1⟩

/-- Supply a certified reducer at an explicit normalization budget. -/
@[reducible] def reduction (fuel : Nat) : OrderReduction leq where
  reduce := fun e => (normalize fuel e).expr
  preserves := normalize_same fuel
  preservesSort := normalize_sort fuel

end Lisa.ExpressionOrder
