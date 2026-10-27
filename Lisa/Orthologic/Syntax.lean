import Lisa.Lambda.Reification

/-! Internal LambdaFOL syntax for orthologic normalization.

Conjunctions are lists, as in Scala's `SimpleExpression`. Disjunction and
existential quantification are represented through negation. Comparison carries
polarity separately, so a negative conjunction or universal needs no duplicate
constructor. Negation can only be applied to a formula.

Binding uses the existing Lambda convention: zero-based indices count enclosing
binders **of the same sort**. In particular, passing an individual quantifier
does not shift a propositional variable. Erasure into `Lambda.Term` reuses its
reification and alpha-renaming proofs. There is no context index on this type.
-/

namespace Lisa.Orthologic

inductive SimpleExpr : LSort → Type where
  | bound : Nat → SimpleExpr s
  | free : Identifier → SimpleExpr s
  | const : Identifier → SimpleExpr s
  | app : SimpleExpr (s >> t) → SimpleExpr s → SimpleExpr t
  | lam (s : LSort) : SimpleExpr t → SimpleExpr (s >> t)
  | top : SimpleExpr prop
  | conj : List (SimpleExpr prop) → SimpleExpr prop
  | all : SimpleExpr prop → SimpleExpr prop
  | equal : SimpleExpr ind → SimpleExpr ind → SimpleExpr prop
  | neg : SimpleExpr prop → SimpleExpr prop
  deriving Repr, Hashable

/-- An internal expression packaged with its sort; no normality invariant. -/
abbrev SomeExpr := (s : LSort) × SimpleExpr s

namespace SimpleExpr

def bot : SimpleExpr prop := .neg .top
def disj (ps : List (SimpleExpr prop)) : SimpleExpr prop := .neg (.conj (ps.map .neg))
def ex (p : SimpleExpr prop) : SimpleExpr prop := .neg (.all (.neg p))

/-- Count nodes, including the children of an n-ary conjunction. -/
def size : SimpleExpr s → Nat
  | .bound _ | .free _ | .const _ | .top => 1
  | .app f a => f.size + a.size + 1
  | .lam _ b | .all b | .neg b => b.size + 1
  | .equal a b => a.size + b.size + 1
  | .conj ps => (ps.map size).sum + 1

theorem size_pos (e : SimpleExpr s) : 0 < e.size := by
  cases e <;> simp [size]

theorem size_lt_conj {p : SimpleExpr prop} {ps : List (SimpleExpr prop)}
    (h : p ∈ ps) : p.size < (conj ps).size := by
  induction ps with
  | nil => simp at h
  | cons q qs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp only [size, List.map_cons, List.sum_cons]; omega
      · have := ih h
        simp only [size, List.map_cons, List.sum_cons] at *
        omega

private def termAnd (p q : Lambda.Term prop) : Lambda.Term prop :=
  .app (.app (.const ⟨"and", 0⟩) p) q

/-- Forget the OL constructors, retaining exactly the Lambda binding convention. -/
def toTerm : SimpleExpr s → Lambda.Term s
  | .bound n => .bound n
  | .free x => .free x
  | .const c => .const c
  | .app f a => .app f.toTerm a.toTerm
  | .lam s b => .lam s b.toTerm
  | .top => .const ⟨"top", 0⟩
  | .conj ps => match ps.map toTerm with
      | [] => .const ⟨"top", 0⟩
      | p :: ps => ps.foldl termAnd p
  | .all b => .app (.const ⟨"forall", 0⟩) (.lam ind b.toTerm)
  | .equal a b => .app (.app (.const ⟨"eq", 0⟩) a.toTerm) b.toTerm
  | .neg p => .app (.const ⟨"not", 0⟩) p.toTerm

def reify (p : SimpleExpr s) (ρ : Lambda.Context) : Expr := p.toTerm.reify ρ

@[simp] theorem reify_const (c : Identifier) (ρ : Lambda.Context) :
    (const (s := s) c).reify ρ = Expr.const ⟨c, s⟩ := by
  simp [reify, toTerm, Lambda.Term.reify]

@[simp] theorem reify_sort (p : SimpleExpr s) (ρ : Lambda.Context) :
    (p.reify ρ).sort = some s := Lambda.Term.reify_sort _ _

@[simp] theorem reify_app (f : SimpleExpr (s >> t)) (a : SimpleExpr s) (ρ : Lambda.Context) :
    (app f a).reify ρ = .app (f.reify ρ) (a.reify ρ) := by
  simp [reify, toTerm, Lambda.Term.reify]

@[simp] theorem reify_neg (p : SimpleExpr prop) (ρ : Lambda.Context) :
    (neg p).reify ρ = Expr.neg (p.reify ρ) := by
  simp [reify, toTerm, Lambda.Term.reify, Expr.neg, SConst.named]

@[simp] theorem reify_conj_pair (p q : SimpleExpr prop) (ρ : Lambda.Context) :
    (conj [p, q]).reify ρ = Expr.and (p.reify ρ) (q.reify ρ) := by
  simp [reify, toTerm, termAnd, Lambda.Term.reify, Expr.and, SConst.named]

@[simp] theorem reify_top (ρ : Lambda.Context) : top.reify ρ = Expr.top := by
  simp [reify, toTerm, Lambda.Term.reify, Expr.top, SConst.named]

@[simp] theorem reify_equal (p q : SimpleExpr ind) (ρ : Lambda.Context) :
    (equal p q).reify ρ = Expr.eq (p.reify ρ) (q.reify ρ) := by
  simp [reify, toTerm, Lambda.Term.reify, Expr.eq, SConst.named]

theorem reify_conj (ps : List (SimpleExpr prop)) (ρ : Lambda.Context) :
    (conj ps).reify ρ = match ps.map (fun p => p.reify ρ) with
      | [] => Expr.top
      | p :: ps => ps.foldl Expr.and p := by
  have fold (ps : List (Lambda.Term prop)) (p : Lambda.Term prop) :
      (ps.foldl termAnd p).reify ρ =
        (ps.map (fun p => p.reify ρ)).foldl Expr.and (p.reify ρ) := by
    induction ps generalizing p with
    | nil => rfl
    | cons q qs ih =>
        simpa [termAnd, Lambda.Term.reify, Expr.and, SConst.named] using ih (termAnd p q)
  cases ps with
  | nil => simp [reify, toTerm, Lambda.Term.reify, Expr.top, SConst.named]
  | cons p ps => simpa [reify, toTerm, List.map_map] using fold (ps.map toTerm) p.toTerm

end SimpleExpr
end Lisa.Orthologic
