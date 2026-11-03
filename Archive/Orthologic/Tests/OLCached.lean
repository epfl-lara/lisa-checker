import Lisa.Orthologic.CachedSoundness

/-! Exact agreement, cache reuse, and binding-sensitive regression tests for the
new LambdaFOL cache. This does not exercise the legacy Nnf/Combined cache. -/
namespace OLCachedTests
open Lisa Lisa.Orthologic
open SimpleExpr

private def p : SimpleExpr prop := .free ⟨"p", 0⟩
private def q : SimpleExpr prop := .free ⟨"q", 0⟩
private def r : SimpleExpr prop := .free ⟨"r", 0⟩
private def a : SimpleExpr ind := .free ⟨"a", 0⟩
private def b : SimpleExpr ind := .free ⟨"b", 0⟩

private def samples : List (SimpleExpr prop) :=
  let leaves := [p, q, .top, .neg p, .neg .top]
  leaves ++ leaves.flatMap (fun x => leaves.flatMap (fun y =>
    [.conj [x, y], .neg (.conj [x, y])])) ++
  [.conj [], .conj [p], .conj [.conj [p, q], p], .neg (.neg p),
   .conj [p, .neg (.conj [p, q])], .equal a b, .equal b a, .equal a a,
   .all (.conj [p, q]), .all p, .neg (.all p)]

-- Exercise every recursive comparison branch, both signs, and all normalization
-- stages with retained caches and with each internal cache disabled.
#eval show IO Unit from do
  for config in ([{}, {comparison := false}, {normalization := false}, {keys := false},
      {comparison := false, normalization := false, keys := false}] : List Cached.Config) do
    let mut cache : Cached.Cache := {config}
    for x in samples do
      let (result, next) := (Cached.computeNormalFormMemo x).run cache
      cache := next
      unless result.val == computeNormalForm x do
        throw (IO.userError "Cached internal normalization changed the output")
      for y in samples do
        let (result, next) := (Cached.latticesEQMemo x y).run cache
        cache := next
        unless result.val == latticesEQ x y do
          throw (IO.userError "Cached internal equivalence changed a decision")
        for s in [false, true] do
          for t in [false, true] do
            let (result, next) := (Cached.polarLEQMemo x s y t).run cache
            cache := next
            unless result.val == polarLEQ x s y t do
              throw (IO.userError "A comparison key lost direction or polarity")

private def named (name : String) (s : LSort) : Expr := .var ⟨⟨name, 0⟩, s⟩
private def x : SVar := ⟨⟨"x", 0⟩, ind⟩
private def y : SVar := ⟨⟨"y", 7⟩, ind⟩
private def z : SVar := ⟨⟨"z", 0⟩, prop⟩
private def pred (name : String) (x : SVar) := Expr.app (named name (ind >> prop)) (.var x)
private def eps (e : Expr) := Expr.epsilon_ (.lam x e)

private def namedSamples : List Expr :=
  let p := named "p" prop
  let q := named "q" prop
  let h := named "h" ((prop >> prop) >> prop)
  [p, q, p.and Expr.top, p.and q, q.and p, p.or q, q.or p, p.imp q, p.iff q,
   .app (.lam z ((Expr.var z).and Expr.top)) p,
   .lam z (.app (named "f" (prop >> prop)) (.var z)), named "f" (prop >> prop),
   Expr.forall_ x ((pred "P" x).and (pred "Q" x)), Expr.forall_ y (pred "P" y),
   Expr.exists_ x ((pred "P" x).and (pred "Q" x)), Expr.exists_ y (pred "P" y),
   eps ((pred "P" x).or (pred "Q" x)), eps ((pred "Q" x).or (pred "P" x)),
   .app h (.lam z ((Expr.var z).and Expr.top)), .app h (.lam z (.var z)),
   .lam x (.lam y (.var x)), .lam x (.lam y (.var y)),
   (named "a" ind).eq (named "b" ind), (named "b" ind).eq (named "a" ind),
   named "a" ind, .app p q]

-- All 16 policies preserve cold and warm results, including malformed syntax,
-- sort mismatch, alpha-renaming, beta/eta, and formulas beneath epsilon/lambdas.
#eval show IO Unit from do
  for preparation in [false, true] do
    for normalization in [false, true] do
      for comparison in [false, true] do
        for keys in [false, true] do
          let config : Cached.Config := {preparation, normalization, comparison, keys}
          let mut cache : Cached.Cache := {config}
          for p in namedSamples do
            let (result, next) := (Cached.normalizeMemo p).run cache
            cache := next
            unless result.val == Orthologic.normalize p &&
                Cached.normalize p config == Orthologic.normalize p do
              throw (IO.userError "Cached named normalization disagrees")
            for q in namedSamples do
              let (same, next) := (Cached.isSameMemo p q).run cache
              cache := next
              let (le, next) := (Cached.isImplyingMemo p q).run cache
              cache := next
              unless same.val == Orthologic.isSame p q && le.val == Orthologic.isImplying p q do
                throw (IO.userError "Reused cache changed a named comparison")
              unless Cached.isSame p q config == same.val && Cached.isImplying p q config == le.val do
                throw (IO.userError "Cold cache disagrees with warm cache")

-- Repeated named comparisons must return from the preparation/comparison cache
-- without computing normal forms, comparison subqueries, or structural keys.
#eval show IO Unit from do
  let p := named "p" prop
  let q := named "q" prop
  let query := Cached.isImplyingMemo (p.and q) p
  let (yes, cold) := query.run ∅
  let (_, warm) := query.run cold
  unless yes.val == some true &&
      warm.stats == {cold.stats with
        preparationHits := cold.stats.preparationHits + 2,
        comparisonHits := cold.stats.comparisonHits + 1} do
    throw (IO.userError "Repeated positive query recomputed work")
  let query := Cached.isImplyingMemo p (p.and q)
  let (no, cold) := query.run warm
  let (_, warm) := query.run cold
  unless no.val == some false &&
      warm.stats == {cold.stats with
        preparationHits := cold.stats.preparationHits + 2,
        comparisonHits := cold.stats.comparisonHits + 1} do
    throw (IO.userError "Negative comparison was not reused")
  let malformed := Expr.app p q
  let (bad, cold) := (Cached.prepareMemo malformed).run warm
  let (_, warm) := (Cached.prepareMemo malformed).run cold
  unless bad.val.isNone &&
      warm.stats == {cold.stats with preparationHits := cold.stats.preparationHits + 1} do
    throw (IO.userError "Malformed input was not cached")

private def sharedDag : Nat → SimpleExpr prop
  | 0 => p
  | n + 1 =>
    let child := sharedDag n
    .conj [child, .conj [child, .free ⟨"extra", n⟩]]

-- Recursion itself shares entries; a cache only around the public entry point
-- would fail these checks. A warm subtree must avoid the entire recursive walk.
#eval show IO Unit from do
  let query := Cached.polarLEQMemo (sharedDag 8) true r true
  let (answer, cache) := query.run ∅
  unless !answer.val && cache.stats.comparisonHits > 0 && cache.stats.comparisonMisses < 40 do
    throw (IO.userError s!"Repeated comparison subtrees were recomputed: {repr cache.stats}")
  let query := Cached.computeNormalFormMemo (sharedDag 5)
  let (_, cache) := query.run ∅
  unless cache.stats.normalizationHits > 0 do
    throw (IO.userError "Repeated normalization subtrees were recomputed")
  let (_, warm) := query.run cache
  unless warm.stats == {cache.stats with normalizationHits := cache.stats.normalizationHits + 1} do
    throw (IO.userError "Warm normalization recomputed a subtree")

-- Exact keys distinguish an explicit application from its logical constructor,
-- even when both erase to the same Lambda term.
private def rawAnd : SimpleExpr prop :=
  .app (.app (.const ⟨"and", 0⟩) p) .top
#guard rawAnd.toTerm = (SimpleExpr.conj [p, .top]).toTerm
#guard rawAnd != SimpleExpr.conj [p, .top]
#eval show IO Unit from do
  let (first, cache) := (Cached.computeNormalFormMemo rawAnd).run ∅
  let (second, _) := (Cached.computeNormalFormMemo (.conj [p, .top])).run cache
  unless first.val == rawAnd && second.val == p do
    throw (IO.userError "Erasure was wrongly used as a normalization cache key")

-- Force collisions in the same dependent-key table used for normal forms.
-- Hidden sorts, binder sorts, identifier indices and constructors still matter.
#eval
  letI : Hashable NormalForm := ⟨fun _ => 0⟩
  show IO Unit from do
  let keys : List NormalForm :=
    [⟨ind, .bound 0⟩, ⟨prop, .bound 0⟩, ⟨prop, .free ⟨"p", 0⟩⟩,
     ⟨prop, .free ⟨"p", 1⟩⟩, ⟨prop, .const ⟨"p", 0⟩⟩,
     ⟨prop, .app (.free (s := ind >> prop) ⟨"f", 0⟩) (.bound 0)⟩,
     ⟨prop, .app (.free (s := prop >> prop) ⟨"f", 0⟩) (.bound 0)⟩,
     ⟨ind >> prop, .lam ind p⟩, ⟨prop >> prop, .lam prop p⟩,
     ⟨prop, rawAnd⟩, ⟨prop, .conj [p, .top]⟩]
  let mut table : Std.DHashMap NormalForm (fun p => Cached.Answer (computeNormalForm p.2)) := ∅
  for key in keys do
    table := table.insert key ⟨computeNormalForm key.2, rfl⟩
  unless table.size == keys.length do
    throw (IO.userError "Distinct keys collapsed under collisions")
  for key in keys do
    let some result := table.get? key | throw (IO.userError "Collision lost an entry")
    unless result.val == computeNormalForm key.2 do
      throw (IO.userError "Collision returned another query's result")

-- Agreement for arbitrary caches, together with soundness in the existing system.
example (cache : Cached.Cache) (p : SimpleExpr s) :
    ((Cached.computeNormalFormMemo p).run' cache).val = computeNormalForm p :=
  ((Cached.computeNormalFormMemo p).run' cache).property

example (cache : Cached.Cache) (p q : Expr)
    (h : ((Cached.isImplyingMemo p q).run' cache).val = some true) :
    Nonempty (Ordered.AlphaBetaEtaProof {p} {q}) :=
  Orthologic.isImplying_sound (by simpa only [Cached.isImplyingMemo_eq] using h)

#print axioms Cached.normalize_eq
#print axioms Cached.isSameMemo_eq
#print axioms Cached.isImplyingMemo_eq
#print axioms Cached.isSame_sound
#print axioms Cached.isImplying_sound

end OLCachedTests
