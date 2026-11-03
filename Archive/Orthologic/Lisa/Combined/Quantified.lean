import Lisa.Combined.OrderedProjection
import Lisa.Combined.Normalize

/-!
Lift quantified body comparisons into propositional comparisons.

Open one well-sorted universal predicate at a fresh variable. Comparing the remaining
bodies in a preorder gives a preorder on expressions with the same prefix.
The outer OL extension then propagates these inequalities through connectives.
Each additional layer permits another alternation of connectives and binders.
-/

namespace Lisa.Orthologic.QuantifiedProjection

open Expr

/-- Retain the binder prefix separately from its propositional body. -/
structure View where
  binders : List SVar
  body : Expr

/-- Open one universal predicate at a certified fresh individual variable. -/
def view : Expr → View
  | .app (.const c) p =>
      if c = .named "forall" ((ind >> prop) >> prop) ∧ p.sort = some (ind >> prop) then
        ⟨[ExpressionOrder.freshVariable p ind], .app p (.var (ExpressionOrder.freshVariable p ind))⟩
      else ⟨[], .app (.const c) p⟩
  | p => ⟨[], p⟩

private theorem rebuild (p : Expr) :
    isSame ExpressionOrder.leq p ((view p).binders.foldr forall_ (view p).body) := by
  fun_cases view p
  · rename_i c f h
    obtain ⟨rfl, hf⟩ := h
    exact ExpressionOrder.same_of_alphaBetaEta (AlphaBetaEta.app (.refl _)
      (AlphaBetaEta.eta (ExpressionOrder.freshVariable f ind) f prop hf
        (ExpressionOrder.freshVariable_not_mem f ind)).symm)
  all_goals exact ⟨.refl _, .refl _⟩

private theorem binders_sorted (p : Expr) :
    ∀ x ∈ (view p).binders, x.sort = ind := by
  fun_cases view p <;> simp_all [ExpressionOrder.freshVariable]

private theorem body_sorted (p : Expr) (h : isFormula p) : isFormula (view p).body := by
  fun_cases view p <;> simp_all [isFormula, Expr.hasSort, Expr.sort, ExpressionOrder.freshVariable]

private theorem prefix_sorted (p : Expr) : (view p).binders ≠ [] → isFormula p := by
  fun_cases view p <;> simp_all [isFormula, Expr.hasSort, Expr.sort]

private theorem fold_sorted (xs : List SVar) (p : Expr)
    (hxs : ∀ x ∈ xs, x.sort = ind) (hp : isFormula p) :
    isFormula (xs.foldr forall_ p) := by
  induction xs with
  | nil => exact hp
  | cons x xs ih =>
      have hx := hxs x (by simp)
      have hs := ih (fun y hy => hxs y (by simp [hy]))
      change (xs.foldr forall_ p).sort = some prop at hs
      simp [List.foldr, isFormula, Expr.hasSort, Expr.forall_, Expr.sort, hx, hs]

/-- Lift a certified body inequality through the common quantifier prefix. -/
theorem lift {p q : Expr} (hprefix : (view p).binders = (view q).binders)
    (h : ExpressionOrder.leq (view p).body (view q).body) : ExpressionOrder.leq p q := by
  have aux (xs : List SVar) (a b : Expr)
      (hxs : ∀ x ∈ xs, x.sort = ind)
      (hs : xs ≠ [] → isFormula a ∧ isFormula b)
      (hab : ExpressionOrder.leq a b) :
      ExpressionOrder.leq (xs.foldr forall_ a) (xs.foldr forall_ b) := by
    induction xs with
    | nil => exact hab
    | cons x xs ih =>
        have hx := hxs x (by simp)
        have ht : ∀ y ∈ xs, y.sort = ind := fun y hy => hxs y (by simp [hy])
        have hs := hs (by simp)
        exact .forallMono x hx (fold_sorted xs a ht hs.1) (fold_sorted xs b ht hs.2)
          (ih ht (fun _ => hs))
  refine .trans (rebuild p).1 (.trans ?_ (rebuild q).2)
  rw [← hprefix]
  apply aux _ _ _ (binders_sorted p) ?_ h
  intro hnonempty
  exact ⟨body_sorted p (prefix_sorted p hnonempty),
    body_sorted q (prefix_sorted q (hprefix ▸ hnonempty))⟩

variable (base : ExprRel) [DecidableRel base] (atoms : Projection.Atoms Expr)

/-- Compare a finite number of binder/connective alternations over the base order. -/
def compare : Nat → Expr → Expr → Bool
  | 0, p, q => decide (base p q)
  | n + 1, p, q =>
      decide ((view p).binders = (view q).binders) &&
        if (view p).binders = [] then decide (base p q)
        else OrderedProjection.check (fun a b => compare n a b = true) atoms
          (view p).body (view q).body

/-- Specify the atomic preorder at the requested comparison depth. -/
abbrev atomicOrder (depth : Nat) : ExprRel := fun p q => compare base atoms depth p q = true

instance (depth : Nat) : DecidableRel (atomicOrder base atoms depth) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

instance [IsPreorder Expr base] (depth : Nat) : IsPreorder Expr (atomicOrder base atoms depth) := by
  induction depth with
  | zero =>
      exact {
        refl := fun p => by simp [atomicOrder, compare]
        trans := fun p q s hp hq => by
          simp only [atomicOrder, compare, decide_eq_true_eq] at *
          exact _root_.trans hp hq }
  | succ n ih =>
      letI := ih
      have iff_order (p q : Expr) : atomicOrder base atoms (n + 1) p q ↔
          (view p).binders = (view q).binders ∧
            (if (view p).binders = [] then base p q else
              OrderedProjection.leq (atomicOrder base atoms n) atoms (view p).body (view q).body) := by
        simp [atomicOrder, compare, OrderedProjection.leq]
      exact {
        refl := fun p => (iff_order p p).mpr ⟨rfl, by split <;> exact refl _⟩
        trans := fun p q s hp hq => by
          obtain ⟨hp, hp'⟩ := (iff_order p q).mp hp
          obtain ⟨hq, hq'⟩ := (iff_order q s).mp hq
          refine (iff_order p s).mpr ⟨hp.trans hq, ?_⟩
          by_cases hn : (view p).binders = []
          · simp only [hn, hp ▸ hn, if_true] at hp' hq' ⊢
            exact _root_.trans hp' hq'
          · simp only [hn, hp ▸ hn, if_false] at hp' hq' ⊢
            exact _root_.trans hp' hq' }

/-- Certify every atomic layer in the reference expression calculus. -/
theorem atomic_sound [IsPreorder Expr base]
    (hbase : ∀ {p q}, base p q → ExpressionOrder.leq p q)
    (hatoms : ∀ a, (atoms a).eval ExpressionOrder.value = ExpressionOrder.value a)
    (depth : Nat) {p q : Expr} (h : atomicOrder base atoms depth p q) :
    ExpressionOrder.leq p q := by
  induction depth generalizing p q with
  | zero => exact hbase (of_decide_eq_true h)
  | succ n ih =>
      have h' : (view p).binders = (view q).binders ∧
          (if (view p).binders = [] then base p q else
            OrderedProjection.leq (atomicOrder base atoms n) atoms (view p).body (view q).body) := by
        simpa [atomicOrder, compare, OrderedProjection.leq] using h
      by_cases hn : (view p).binders = []
      · exact hbase (by simpa only [hn, if_true] using h'.2)
      · exact lift h'.1 (OrderedProjection.sound _ atoms ExpressionOrder.interpretation ExpressionOrder.value
          (fun _ _ h => ih h) hatoms (by simpa only [hn, if_false] using h'.2))

end Lisa.Orthologic.QuantifiedProjection
