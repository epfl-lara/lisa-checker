import Lisa.Combined.Projection
import Lisa.Combined.OrderedProjection
import Lisa.Combined.Lambda
import Lisa.Combined.Normalize
import Lisa.Combined.Equality
import Lisa.Combined.Reflection
import Lisa.Combined.Quantified
import Lisa.Checker.Check
import Lisa.Checker.Binary

/-!
Compose total lambda normalization, certified contextual simplification, and OL.

Spend the contextual budget on opaque leaves, never on their propositional
wrappers. Retain contextual congruence as the fast path and lift quantified
inequalities through certified atomic preorders as a fallback. The resulting
acceptance relation is reference-sound, not a decision of the full reference order.
-/

namespace Lisa.Combined

open Expr Orthologic

/-- Canonicalize binders again after simplification introduces or changes abstractions. -/
def normalizeAtom (budget : Nat) (a : Expr) : ExpressionOrder.ReductionResult a :=
  let first := ExpressionOrder.ReductionResult.converted
    (ExpressionOrder.reduceLambda_alphaBetaEta a).symm
  let simplified := first.andThen (ExpressionOrder.normalize budget first.expr)
  let builtins := simplified.andThen (ExpressionOrder.simplifyBuiltins simplified.expr)
  let converted := builtins.andThen (.converted
    (ExpressionOrder.reduceLambda_alphaBetaEta builtins.expr).symm)
  converted.andThen (ExpressionOrder.orientEqualities converted.expr)

/-- Normalize each atom while retaining any exposed propositional structure. -/
def atoms (budget : Nat) (a : Expr) : Nnf Expr :=
  (reify (normalizeAtom budget a).expr).toNnf

/-- Retain constructor structure after certified leaf normalization. -/
def contextualAtoms (budget : Nat) (a : Expr) :
    Contextual.Term Expr ContextualReflection.Constructor :=
  ContextualReflection.reify (normalizeAtom budget a).expr

/-- Retain exact decisions about this algorithm, not refutations of the reference order. -/
abbrev leq (budget : Nat) : ExprRel := ContextualProjection.leq (contextualAtoms budget)

private theorem atoms_contextual (budget : Nat) (a : Expr) :
    (atoms budget a).eval ContextualReflection.value =
      Contextual.value (contextualAtoms budget a) := by
  rw [atoms, Formula.eval_toNnf]
  rw [eval_reify ContextualReflection.algebra]
  rfl

private theorem normalized_sound (budget : Nat) (p q : Expr)
    (h : Nnf.checkNormalizedLe (Projection.project (atoms budget) p)
      (Projection.project (atoms budget) q) = true) : leq budget p q := by
  apply (ContextualProjection.check_iff_eval_le (contextualAtoms budget) p q).mpr
  have hv := Nnf.checkNormalizedLe_sound ContextualReflection.value h
  rw [Projection.eval_project, Projection.eval_project] at hv
  simpa only [Projection.eval, atoms_contextual, ContextualProjection.eval] using hv

/-- Compare normalized independent atoms before exact contextual comparison. -/
def check (budget : Nat) (p q : Expr) : Bool :=
  if p = q then true
  else if Nnf.checkNormalizedLe (Projection.project (atoms budget) p) (Projection.project (atoms budget) q)
    then true
  else ContextualProjection.check (contextualAtoms budget) p q

theorem check_iff (budget : Nat) (p q : Expr) : check budget p q = true ↔ leq budget p q := by
  unfold check
  split
  · rename_i h
    subst q
    simp only [true_iff]
    exact (ContextualProjection.check_iff_eval_le _ _ _).mpr le_rfl
  · split
    · rename_i h
      simp only [true_iff]
      exact normalized_sound budget p q h
    · rfl

instance (priority := 1100) (budget : Nat) : DecidableRel (leq budget) := fun p q =>
  decidable_of_iff (check budget p q = true) (check_iff budget p q)

instance (budget : Nat) : CheckerOrder (leq budget) := CheckerOrder.of _

/-- Preserve exact contextual answers while short-circuiting certified positive queries. -/
theorem check_eq_contextual (budget : Nat) (p q : Expr) :
    check budget p q = ContextualProjection.check (contextualAtoms budget) p q :=
  Bool.eq_iff_iff.mpr (check_iff budget p q)

private theorem atoms_sound (budget : Nat) (a : Expr) :
    (atoms budget a).eval ExpressionOrder.value = ExpressionOrder.value a := by
  rw [atoms, Formula.eval_toNnf]
  change (reify (normalizeAtom budget a).expr).eval
    ExpressionOrder.interpretation.eval =
      ExpressionOrder.interpretation.eval a
  rw [eval_reify ExpressionOrder.interpretation]
  exact (ExpressionOrder.interpretation.same_iff.mp (normalizeAtom budget a).same).symm

private theorem contextualAtoms_sound (budget : Nat) (a : Expr) :
    (contextualAtoms budget a).eval ExpressionOrder.value
      ContextualReflection.unary ContextualReflection.binary = ExpressionOrder.value a := by
  rw [contextualAtoms, ContextualReflection.eval_reify]
  exact (ExpressionOrder.interpretation.same_iff.mp (normalizeAtom budget a).same).symm

/-- Certify every successful comparison in the original combined reference calculus. -/
theorem sound {budget : Nat} {p q : Expr} (h : leq budget p q) :
    ExpressionOrder.leq p q :=
  ContextualProjection.sound ExpressionOrder.interpretation (contextualAtoms budget) ExpressionOrder.value
    ContextualReflection.unary ContextualReflection.binary (contextualAtoms_sound budget) h

namespace Ordered

variable (r : Expr → Expr → Prop) [DecidableRel r]

/-- Compare normalized projections with a supplied decidable atomic relation. -/
def check (budget : Nat) (p q : Expr) : Bool :=
  OrderedProjection.check r (atoms budget) p q

/-- Lift an atomic preorder to the combined checker interfaces. -/
abbrev leq (budget : Nat) : ExprRel := OrderedProjection.leq r (atoms budget)

/-- Certify accepted comparisons when every atomic inequality is reference-sound. -/
theorem sound [IsPreorder Expr r]
    (hsound : ∀ {p q}, r p q → ExpressionOrder.leq p q)
    {budget : Nat} {p q : Expr} (h : leq r budget p q) : ExpressionOrder.leq p q :=
  OrderedProjection.sound r (atoms budget) ExpressionOrder.interpretation ExpressionOrder.value
    (fun _ _ h => hsound h) (atoms_sound budget) h

end Ordered

namespace Quantified

/-- Lift quantified body comparisons through the normalized propositional shell. -/
abbrev leq (budget depth : Nat) : ExprRel :=
  OrderedProjection.leq
    (QuantifiedProjection.atomicOrder (Combined.leq budget) (atoms budget) depth) (atoms budget)

/-- Compare with a sound, finite number of binder/connective alternations. -/
def check (budget depth : Nat) (p q : Expr) : Bool :=
  if p = q then true else
  if Nnf.checkNormalizedLe (Projection.project (atoms budget) p)
      (Projection.project (atoms budget) q) then true
  else OrderedProjection.check
    (QuantifiedProjection.atomicOrder (Combined.leq budget) (atoms budget) depth) (atoms budget) p q

theorem check_iff (budget depth : Nat) (p q : Expr) :
    check budget depth p q = true ↔ leq budget depth p q := by
  unfold check
  split
  · rename_i heq
    subst q
    simp only [true_iff]
    exact refl _
  · split
    · rename_i h
      simp only [true_iff]
      apply (OrderedProjection.leq_iff _ _ _ _).mpr
      intro L _ v _
      simpa only [Projection.eval_project] using Nnf.checkNormalizedLe_sound v h
    · rfl

instance (priority := 1100) (budget depth : Nat) : DecidableRel (leq budget depth) :=
  fun p q => decidable_of_iff (check budget depth p q = true) (check_iff budget depth p q)

/-- Certify quantified comparisons in the unchanged reference expression calculus. -/
theorem sound {budget depth : Nat} {p q : Expr} (h : leq budget depth p q) :
    ExpressionOrder.leq p q :=
  OrderedProjection.sound _ (atoms budget) ExpressionOrder.interpretation ExpressionOrder.value
    (fun _ _ h => QuantifiedProjection.atomic_sound (Combined.leq budget) (atoms budget)
      (fun h => Combined.sound h) (atoms_sound budget) depth h)
    (atoms_sound budget) h

instance (budget depth : Nat) : CheckerOrder (leq budget depth) := CheckerOrder.of _

end Quantified

namespace Replay

/-!
The union of two preorders need not be transitive. Use only the encoding and
reduction interfaces consumed by the checker; transfer accepted certificates
to the reference order before using the proof-system equivalence theorems.
-/

/-- Accept either certified backend without asserting completeness of the reference order. -/
abbrev leq (budget : Nat) : ExprRel := fun p q =>
  Combined.leq budget p q ∨ Quantified.leq budget (budget + 1) p q

/-- Retain contextual successes before trying quantified atomic inequalities. -/
def check (budget : Nat) (p q : Expr) : Bool :=
  Combined.check budget p q || Quantified.check budget (budget + 1) p q

theorem check_iff (budget : Nat) (p q : Expr) :
    check budget p q = true ↔ leq budget p q := by
  simp only [check, Bool.or_eq_true, Combined.check_iff, Quantified.check_iff, leq]

instance (budget : Nat) : DecidableRel (leq budget) := fun p q =>
  decidable_of_iff (check budget p q = true) (check_iff budget p q)

instance (budget : Nat) : SequentEncoding (leq budget) where
  compare pre post p :=
    ⟨or_congr (SequentEncoding.compare (leq := Combined.leq budget) pre post p).1
        (SequentEncoding.compare (leq := Quantified.leq budget (budget + 1)) pre post p).1,
      or_congr (SequentEncoding.compare (leq := Combined.leq budget) pre post p).2
        (SequentEncoding.compare (leq := Quantified.leq budget (budget + 1)) pre post p).2⟩

instance (budget : Nat) : OrderReduction (leq budget) where
  reduce := reduceExpr
  preserves p :=
    let h := same_reduceExpr (ContextualProjection.interpretation (contextualAtoms budget)) p
    ⟨Or.inl h.1, Or.inl h.2⟩
  preservesSort := sort_reduceExpr
  reflect p q h :=
    let hsame := OrderReduction.sound (leq := Combined.leq budget) p q h
    ⟨Or.inl hsame.1, Or.inl hsame.2⟩

/-- Transfer either successful comparison to the original reference calculus. -/
theorem sound {budget : Nat} {p q : Expr} (h : leq budget p q) : ExpressionOrder.leq p q :=
  h.elim Combined.sound Quantified.sound

/-- Use contextual matching for routine rules, transferring successful matches into replay. -/
def matching (budget : Nat) : Imported.Checker.Matching (leq budget) where
  source := Combined.leq budget
  reduction := inferInstance
  decision := inferInstance
  simulation := Or.inl

instance (budget : Nat) : CheckerOrder (leq budget) := CheckerOrder.of _

end Replay

/-- Check a linear proof and return its erased Imported certificate. -/
def checkProof (budget : Nat) (proof : Imported.Checker.LinearProof)
    (imports : Array Imported.Checker.Statement := #[]) :=
  Imported.Checker.check (leq := Replay.leq budget) proof imports (Replay.matching budget)

/-- Require the requested conclusion and no remaining assumptions. -/
def checkClosed (budget : Nat) (proof : Imported.Checker.LinearProof)
    (target : Imported.Checker.Statement)
    (imports : Array Imported.Checker.Statement := #[]) :=
  Imported.Checker.checkClosed (leq := Replay.leq budget) proof target imports (Replay.matching budget)

/-- Read paged binary proof streams with the same certified executable backend. -/
def checkFiles (budget : Nat) (treePath proofPath : System.FilePath) (diagnostics := false) :=
  Imported.Binary.checkFiles (leq := Replay.leq budget) treePath proofPath diagnostics (Replay.matching budget)

section Reference

/-- Transfer positive comparisons to the reference relation. -/
def simulation (budget : Nat) : Subrelation (leq budget) ExpressionOrder.leq :=
  sound

/-- Transfer quantified comparisons to the reference relation. -/
def Quantified.simulation (budget depth : Nat) :
    Subrelation (Quantified.leq budget depth) ExpressionOrder.leq :=
  Quantified.sound

/-- Transfer all replay comparisons to the reference relation. -/
def Replay.simulation (budget : Nat) : Subrelation (Replay.leq budget) ExpressionOrder.leq :=
  Replay.sound

/-- Transfer certificates from any reference-sound normalized atomic preorder. -/
def Ordered.simulation (r : Expr → Expr → Prop) [DecidableRel r] [IsPreorder Expr r]
    (hsound : ∀ {p q}, r p q → ExpressionOrder.leq p q) (budget : Nat) :
    Subrelation (Ordered.leq r budget) ExpressionOrder.leq :=
  Ordered.sound r hsound

/-- Select the reference calculus independently of any reduction algorithm. -/
abbrev ReferenceProof (target : Imported.Checker.Statement) :=
  Weakened.ProofTree ExpressionOrder.leq target.sequent.1 target.sequent.2

/-- Turn any accepted closed certificate into a proof in the original reference calculus. -/
theorem certificate_sound {budget : Nat} {target : Imported.Checker.Statement}
    (result : Imported.Checker.ClosedChecked (Replay.leq budget) target) :
    Nonempty (ReferenceProof target) :=
  result.resolveWith (Replay.simulation budget)

/-- Transfer a closed ordered-atom certificate to the same reference proof system. -/
theorem Ordered.certificate_sound (r : Expr → Expr → Prop)
    [DecidableRel r] [IsPreorder Expr r]
    (hsound : ∀ {p q}, r p q → ExpressionOrder.leq p q)
    {budget : Nat} {target : Imported.Checker.Statement}
    (result : Imported.Checker.ClosedChecked (Ordered.leq r budget) target) :
    Nonempty (ReferenceProof target) :=
  result.resolveWith (Ordered.simulation r hsound budget)

end Reference

end Lisa.Combined
