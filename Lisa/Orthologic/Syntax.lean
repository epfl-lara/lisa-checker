import Lisa.AlphaBetaEtaNormalization.Algorithm

/-! Internal LambdaFOL syntax for orthologic normalization.

Conjunctions are lists, as in Scala's `SimpleExpression`. Disjunction and
existential quantification are represented through negation. Comparison carries
polarity separately, so a negative conjunction or universal needs no duplicate
constructor. Negation can only be applied to a formula.

Binding uses the existing AlphaBetaEtaNormalization.Algorithm convention: zero-based indices count enclosing
binders **of the same sort**. In particular, passing an individual quantifier
does not shift a propositional variable. Erasure into `AlphaBetaEtaNormalization.Algorithm.Term` reuses its
reification and alpha-renaming proofs.
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

def termAnd (p q : AlphaBetaEtaNormalization.Algorithm.Term prop) : AlphaBetaEtaNormalization.Algorithm.Term prop :=
  .app (.app (.const ⟨"and", 0⟩) p) q

/-- Forget the OL constructors, retaining exactly the AlphaBetaEtaNormalization.Algorithm binding convention. -/
def toTerm : SimpleExpr s → AlphaBetaEtaNormalization.Algorithm.Term s
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

def reify (p : SimpleExpr s) (ρ : AlphaBetaEtaNormalization.Algorithm.Context) : Expr := p.toTerm.reify ρ

end SimpleExpr
end Lisa.Orthologic
