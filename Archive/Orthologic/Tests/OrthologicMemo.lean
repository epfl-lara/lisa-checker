import Lisa.Orthologic.Memo
import Lisa.Orthologic.Decision
import Lisa.Orthologic.NormalizationComplete
import Lisa.Orthologic.Substitution

open Lisa.Orthologic

namespace Lisa.Tests.OrthologicMemo

private def a : Nnf Nat := .lit 0 false
private def b : Nnf Nat := .lit 1 false
private def c : Nnf Nat := .lit 2 false

private def samples : List (Nnf Nat) :=
  let leaves := [.bot, .top, a, a.compl, b, b.compl]
  leaves ++ leaves.flatMap (fun p => leaves.flatMap (fun q => [.meet p q, .join p q])) ++
    [.meet a (.join b c), .join (.meet a b) (.meet a c),
     .meet (.join a b) (.meet a.compl b.compl),
     .join (.meet a b) (.join a.compl b.compl),
     .meet a (.join (.meet a b) (.meet a b.compl)),
     .join a (.meet (.join a b) (.join a b.compl))]

-- Check all decisions under cold and reused caches, and each cache separately.
#eval show IO Unit from do
  for config in ([{}, { comparison := false }, { normalization := false },
      { normalization := false, comparison := false }] : List Nnf.MemoConfig) do
    let mut cache : Nnf.Memo Nat := { config }
    for p in samples do
      let (normal, next) := (Nnf.normalizeMemo p).run cache
      cache := next
      unless normal.val == p.normalize do
        throw (IO.userError "Cached normalization disagrees with uncached normalization")
      for q in samples do
        let expected := Nnf.checkNormalizedLe p q
        unless Nnf.checkCachedLe p q == expected do
          throw (IO.userError "Cold cached containment disagrees with uncached containment")
        let (answer, next) := (Nnf.checkMemo p q).run cache
        cache := next
        unless answer.val == expected do
          throw (IO.userError "Reused cached containment disagrees with uncached containment")
        for side in [Nnf.ComparisonSide.both, .project, .inject] do
          let (answer, next) := (Nnf.compareMemo side p q).run cache
          cache := next
          unless answer.val == Nnf.structuralCompare side p q do
            throw (IO.userError "Cached comparison changed a flattening-mode decision")

-- Cache both outcomes, preserve direction, and return on a hit without recursion.
#eval show IO Unit from do
  let query := Nnf.checkMemo (.meet a b) a
  let (positive, cache) := query.run ∅
  unless positive.val do throw (IO.userError "Expected positive containment")
  let (_, warm) := query.run cache
  unless warm.stats.normalizationHits == cache.stats.normalizationHits + 2 &&
      warm.stats.comparisonHits == cache.stats.comparisonHits + 1 &&
      warm.stats.normalizationMisses == cache.stats.normalizationMisses &&
      warm.stats.comparisonMisses == cache.stats.comparisonMisses do
    throw (IO.userError "Repeated query recomputed cached work")
  let (negative, cache) := (Nnf.checkMemo a (.meet a b)).run warm
  if negative.val then throw (IO.userError "Reversed containment accepted")
  let (_, again) := (Nnf.checkMemo a (.meet a b)).run cache
  unless again.stats.comparisonHits == cache.stats.comparisonHits + 1 &&
      again.stats.comparisonMisses == cache.stats.comparisonMisses do
    throw (IO.userError "Negative comparison was not reused")

private structure CollisionAtom where
  index : Nat
  deriving DecidableEq

private instance : Hashable CollisionAtom := ⟨fun _ => 0⟩

private def sharedDag : Nat → Nnf Nat
  | 0 => a
  | n + 1 =>
      let previous := sharedDag n
      .meet (.join previous (.lit (2 * n + 1) false))
        (.join previous (.lit (2 * n + 2) false))

-- Reuse repeated negative DAG subproblems and keep mode-sensitive answers apart.
#eval show IO Unit from do
  let (answer, cache) := (Nnf.compareMemo .both (sharedDag 8) (.lit 100 false)).run ∅
  unless !answer.val && cache.stats.comparisonHits > 0 &&
      cache.stats.comparisonMisses ≤ 30 do
    throw (IO.userError s!"Shared comparison was not memoized: {repr cache.stats}")
  let p := Nnf.meet a b
  let q := Nnf.join p c
  let (both, cache) := (Nnf.compareMemo .both p q).run ∅
  let (project, _) := (Nnf.compareMemo .project p q).run cache
  unless both.val && !project.val do
    throw (IO.userError "Comparison mode was lost from the cache key")

-- Force every atom hash to collide; equality must still distinguish decisions.
#eval show IO Unit from do
  let formulas := samples.map fun p => p.bind fun i => .lit ⟨i⟩ false
  let mut cache : Nnf.Memo CollisionAtom := ∅
  for p in formulas do
    for q in formulas do
      let (answer, next) := (Nnf.checkMemo p q).run cache
      cache := next
      unless answer.val == Nnf.checkNormalizedLe p q do
        throw (IO.userError "Hash collision changed containment")

-- Exact agreement holds for every well-typed cache, not only empty ones.
example (cache : Nnf.Memo Nat) (p : Nnf Nat) :
    ((Nnf.normalizeMemo p).run' cache).val = p.normalize :=
  ((Nnf.normalizeMemo p).run' cache).property

example (cache : Nnf.Memo Nat) (p q : Nnf Nat) :
    ((Nnf.checkMemo p q).run' cache).val = Nnf.checkNormalizedLe p q :=
  ((Nnf.checkMemo p q).run' cache).property

example (p q : Nnf Nat) :
    Nnf.checkCachedLe p q = Calculus.decideLe p q :=
  Nnf.checkCachedLe_eq p q

#print axioms Nnf.checkCachedLe_eq

end Lisa.Tests.OrthologicMemo
