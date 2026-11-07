import Lisa.Orthologic.Equivalence

/-! The relation used in checker certificates is justified by actual Ordered
αβη proofs. The executable OL algorithm is a sound, incomplete test for it;
there is deliberately no `DecidableRel` instance for this relation. -/

namespace Imported.Checker
open Lisa Expr Orthologic

def ProofRelation (p q : Expr) : Prop :=
  p.sort = q.sort ∧ ∀ s, p.hasSort s →
    match s with
    | .prop => Nonempty (Ordered.AlphaBetaEtaProof {p} {q})
    | s => ContextEq s p q

end Imported.Checker
