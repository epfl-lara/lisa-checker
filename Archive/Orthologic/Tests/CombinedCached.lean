import Lisa.CombinedCached

namespace Lisa.Tests.CombinedCached

open Expr Orthologic

private def samples : List Expr :=
  let a := Expr.const (.named "A" prop)
  let b := Expr.const (.named "B" prop)
  let x : SVar := ⟨⟨"x", 0⟩, ind⟩
  let y : SVar := ⟨⟨"y", 1⟩, ind⟩
  let z : SVar := ⟨⟨"z", 0⟩, prop⟩
  let f := Expr.const (.named "f" (prop >> prop))
  [a, b, top, bot, and a b, or a b, and a (neg a),
    .app (.lam z (.var z)) a, .app f (and a top), .app f a,
    forall_ x (and a b), forall_ y a, forall_ x (iff a b), forall_ y (imp b a)]

-- Include beta conversion, opaque congruence, and positive/negative quantified cases.
#eval show IO Unit from do
  for budget in [0, 2] do
    for config in ([{}, { comparison := false }, { normalization := false }] : List Nnf.MemoConfig) do
      for p in samples do
        for q in samples do
          unless Lisa.Combined.Cached.check config budget p q == Lisa.Combined.Replay.check budget p q do
            throw (IO.userError s!"Cached replay changed a decision: {repr p}, {repr q}")

example (config : Nnf.MemoConfig) (budget : Nat) (p q : Expr) :
    Lisa.Combined.Cached.check config budget p q = Lisa.Combined.Replay.check budget p q :=
  Lisa.Combined.Cached.check_eq config budget p q

-- Preserve malformed-proof failures as well as conclusions and assumptions.
#eval show IO Unit from do
  let a := Expr.const (.named "A" prop)
  let b := Expr.const (.named "B" prop)
  let hyp : Imported.Checker.Step := ⟨⟨[a], [a]⟩, .hypothesis a⟩
  let proofs : List Imported.Checker.LinearProof :=
    [#[], #[hyp], #[hyp, ⟨⟨[], [imp a a]⟩, .rightImp 0 a a⟩],
      #[hyp, ⟨⟨[a, b], [a]⟩, .weakening 0⟩],
      #[⟨⟨[a], [a]⟩, .restate 1⟩, hyp],
      #[hyp, ⟨⟨[], [b]⟩, .restate 0⟩],
      #[⟨⟨[a], [b]⟩, .hypothesis a⟩],
      #[⟨⟨[a], [a]⟩, .assume⟩, hyp, ⟨⟨[a], [a]⟩, .discharge 0 1⟩]]
  for config in ([{}, { comparison := false }, { normalization := false }] : List Nnf.MemoConfig) do
    for proof in proofs do
      match Lisa.Combined.checkProof 2 proof, Lisa.Combined.Cached.checkProof config 2 proof with
      | .error expected, .error actual =>
          unless expected == actual do throw (IO.userError "Cached checker changed a failure")
      | .ok expected, .ok actual =>
          unless expected.statement == actual.statement && expected.assumptions == actual.assumptions do
            throw (IO.userError "Cached checker changed a certificate's conclusion or assumptions")
      | _, _ => throw (IO.userError "Cached checker changed proof acceptance")

#print axioms Lisa.Combined.Cached.check_eq

end Lisa.Tests.CombinedCached
