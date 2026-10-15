import Lisa.Syntax
import Std.Data.HashMap.Basic

namespace Lisa.Tests.StoredHash

-- Keep recursive specifications independent of the stored fields.
private def sortHash : LSort → UInt64
  | .ind => 0
  | .prop => 1
  | .arrow a b => mixHash (mixHash 2 (sortHash a)) (sortHash b)

private def exprHash : Expr → UInt64
  | .var x => mixHash 0 (hash x)
  | .const c => mixHash 1 (hash c)
  | .app f a => mixHash (mixHash 2 (exprHash f)) (exprHash a)
  | .lam x body => mixHash (mixHash 3 (hash x)) (exprHash body)

theorem sortHash_eq (s : LSort) : s.cachedHash = sortHash s := by
  induction s <;> simp_all [LSort.cachedHash, sortHash]

theorem exprHash_eq (e : Expr) : e.cachedHash = exprHash e := by
  induction e <;> simp_all [Expr.cachedHash, exprHash]

private def samples : List Expr :=
  let x : SVar := ⟨⟨"x", 0⟩, .ind⟩
  let y : SVar := ⟨⟨"x", 1⟩, .ind⟩
  let p : SVar := ⟨⟨"x", 0⟩, .prop⟩
  let f : SConst := ⟨⟨"f", 0⟩, .arrow .ind .ind⟩
  let deep := (List.range 64).foldl (fun s _ => LSort.arrow s s) .ind
  let z : SVar := ⟨⟨"z", 9⟩, deep⟩
  [.var x, .var y, .var p, .var z, .const f,
    .app (.const f) (.var x), .lam x (.var x), .lam y (.var y),
    .lam x (.var y), .lam p (.var p), .lam z (.var z)]

#eval show IO Unit from do
  for a in [LSort.ind, .prop, .arrow .ind .prop] do
    for b in [LSort.ind, .prop, .arrow .prop .ind] do
      let s := LSort.arrow a b
      unless hash s == sortHash s do
        throw (IO.userError "Stored sort hash differs from recursive hashing")
  -- Exercise shared construction, reconstruction, and growing hash tables.
  let leaf := Expr.var ⟨⟨"shared", 0⟩, .ind⟩
  let dag := (List.range 12).foldl (fun e _ => Expr.app e e) leaf
  unless hash dag == exprHash dag do
    throw (IO.userError "Stored DAG hash differs from recursive hashing")
  let mut table : Std.HashMap Expr Nat := ∅
  for n in List.range 512 do
    let e := Expr.var ⟨⟨"key", n⟩, .arrow .ind .prop⟩
    table := table.insert e n
  for n in List.range 512 do
    let e := Expr.var ⟨⟨"key", n⟩, .arrow .ind .prop⟩
    unless table[e]? == some n do
      throw (IO.userError "Stored hash failed after table expansion")
  for e in samples do
    unless hash e == e.cachedHash && hash e == exprHash e do
      throw (IO.userError "Hashable disagrees with structural hashing")
  unless (samples.take 3).eraseDups.length == 3 do
    throw (IO.userError "Hashing changed identifier or sort equality")

#print axioms sortHash_eq
#print axioms exprHash_eq

end Lisa.Tests.StoredHash
