import Lisa.Orthologic.Normalize
import Std.Data.DHashMap.Basic

/-!
Cache exact answers to normalization and structural comparison. Keep the
uncached algorithms as specifications and erase agreement certificates at
compilation. Scope each state to a query or an explicitly managed session.
-/

namespace Lisa.Orthologic.Nnf

variable {α : Type} [DecidableEq α] [Hashable α]

/-- Select which answers to retain in a cache session. -/
structure MemoConfig where
  normalization : Bool := true
  comparison : Bool := true
  deriving Repr

/-- Count cache reuse separately from the number of retained entries. -/
structure MemoStats where
  normalizationHits : Nat := 0
  normalizationMisses : Nat := 0
  comparisonHits : Nat := 0
  comparisonMisses : Nat := 0
  deriving Repr, BEq

/-- Retain normal forms and directed comparison answers with exact certificates. -/
structure Memo (α : Type) [DecidableEq α] [Hashable α] where
  config : MemoConfig := {}
  stats : MemoStats := {}
  normalForms : Std.DHashMap (Nnf α) (fun p => {n : Nnf α // n = p.normalize}) := ∅
  comparisons : Std.DHashMap (ComparisonSide × Nnf α × Nnf α)
    (fun key => {b : Bool // b = structuralCompare key.1 key.2.1 key.2.2}) := ∅

instance : EmptyCollection (Memo α) := ⟨{}⟩

private def andAnswer {a b : Bool} (x : {r : Bool // r = a})
    (next : StateM (Memo α) {r : Bool // r = b}) :
    StateM (Memo α) {r : Bool // r = (a && b)} := do
  if h : x.val = true then
    let y ← next
    return ⟨y.val, by simp [← x.property, h, y.property]⟩
  else
    return ⟨false, by simp [← x.property, Bool.eq_false_iff.mpr h]⟩

private def orAnswer {a b : Bool} (x : {r : Bool // r = a})
    (next : StateM (Memo α) {r : Bool // r = b}) :
    StateM (Memo α) {r : Bool // r = (a || b)} := do
  if h : x.val = true then
    return ⟨true, by simp [← x.property, h]⟩
  else
    let y ← next
    return ⟨y.val, by simp [← x.property, Bool.eq_false_iff.mpr h, y.property]⟩

/-- Memoize recursive comparisons, including negative answers and flattening mode. -/
def compareMemo (side : ComparisonSide) (p q : Nnf α) :
    StateM (Memo α) {b : Bool // b = structuralCompare side p q} := by
  refine do
    if !(← get).config.comparison then
      modify fun cache => { cache with stats.comparisonMisses := cache.stats.comparisonMisses + 1 }
      return ⟨structuralCompare side p q, rfl⟩
    let key := (side, p, q)
    if let some answer := (← get).comparisons.get? key then
      modify fun cache => { cache with stats.comparisonHits := cache.stats.comparisonHits + 1 }
      return answer
    modify fun cache => { cache with stats.comparisonMisses := cache.stats.comparisonMisses + 1 }
    let answer ← ?_
    modify fun cache => { cache with comparisons := cache.comparisons.insert key answer }
    return answer
  rw [structuralCompare.eq_def]
  split
  · exact pure ⟨true, rfl⟩
  · split
    next _ _ _ a b _ => exact do
      orAnswer (← compareMemo .project a q) (compareMemo .project b q)
    next _ _ _ a b _ => exact do
      orAnswer (← compareMemo .inject p a) (compareMemo .inject p b)
    next => exact pure ⟨true, rfl⟩
    next => exact pure ⟨true, rfl⟩
    next _ _ _ a b _ _ _ => exact do
      andAnswer (← compareMemo .both p a) (compareMemo .both p b)
    next _ _ _ a b _ _ _ _ => exact do
      andAnswer (← compareMemo .both a q) (compareMemo .both b q)
    next _ _ _ a b c d _ => exact do
      let first ← orAnswer (← compareMemo .project a (.join c d))
        (compareMemo .project b (.join c d))
      let second ← orAnswer first (compareMemo .inject (.meet a b) c)
      orAnswer second (compareMemo .inject (.meet a b) d)
    next _ _ _ a b _ _ _ _ _ _ => exact do
      orAnswer (← compareMemo .both a q) (compareMemo .both b q)
    next _ _ _ a b _ _ _ _ _ _ => exact do
      orAnswer (← compareMemo .both p a) (compareMemo .both p b)
    next => exact pure ⟨false, rfl⟩
termination_by p.size + q.size
decreasing_by all_goals simp_all only [size]; omega

private def refineFactorMemo (context p : Nnf α) :
    StateM (Memo α) {ps : List (Nnf α) // ps = refineFactor context p} :=
  match p with
  | .meet p q => do
      let left ← refineFactorMemo context p
      let right ← refineFactorMemo context q
      return ⟨left.val ++ right.val, by simp [refineFactor, left.property, right.property]⟩
  | .join p q => do
      let left ← compareMemo .both context p
      if h : left.val = true then
        let result ← refineFactorMemo context p
        return ⟨result.val, by
          simp [refineFactor, structuralLe, ← left.property, h, result.property]⟩
      else
        let right ← compareMemo .both context q
        if k : right.val = true then
          let result ← refineFactorMemo context q
          return ⟨result.val, by
            simp [refineFactor, structuralLe, ← left.property, ← right.property,
              h, k, result.property]⟩
        else
          return ⟨[.join p q], by
            simp [refineFactor, structuralLe, ← left.property, ← right.property, h, k]⟩
  | .top => pure ⟨[], rfl⟩
  | .bot => pure ⟨[.bot], rfl⟩
  | .lit a s => pure ⟨[.lit a s], rfl⟩

private def refineFactorsMemo (context : Nnf α) (ps : List (Nnf α)) :
    StateM (Memo α) {qs : List (Nnf α) // qs = refineFactors context ps} :=
  match ps with
  | [] => pure ⟨[], rfl⟩
  | p :: ps => do
      let first ← refineFactorMemo context p
      let rest ← refineFactorsMemo context ps
      return ⟨first.val ++ rest.val, by
        simp [refineFactors, first.property, rest.property]⟩

private def pruneFactorsMemo (accepted ps : List (Nnf α)) :
    StateM (Memo α) {qs : List (Nnf α) // qs = pruneFactors accepted ps} :=
  match ps with
  | [] => pure ⟨accepted, rfl⟩
  | p :: ps => do
      let answer ← compareMemo .both (meetAll (ps ++ accepted)) p
      if h : answer.val = true then
        let rest ← pruneFactorsMemo accepted ps
        return ⟨rest.val, by simp [pruneFactors, structuralLe, ← answer.property, h, rest.property]⟩
      else
        let rest ← pruneFactorsMemo (p :: accepted) ps
        return ⟨rest.val, by simp [pruneFactors, structuralLe, ← answer.property, h, rest.property]⟩

/-- Reuse comparison answers during refinement, pruning and contradiction checks. -/
def normalMeetMemo (ps : List (Nnf α)) :
    StateM (Memo α) {n : Nnf α // n = normalMeet ps} := do
  let refined ← refineFactorsMemo (meetAll ps) ps
  let pruned ← pruneFactorsMemo [] refined.val
  let result := meetAll pruned.val.reverse
  let answer ← compareMemo .both result result.compl
  return ⟨if answer.val then .bot else result, by
    simp only [normalMeet, structuralLe, ← refined.property, ← pruned.property,
      ← answer.property, result]⟩

private def smartMeetMemo (p q : Nnf α) :
    StateM (Memo α) {n : Nnf α // n = smartMeet p q} :=
  normalMeetMemo (p.meetFactors ++ q.meetFactors)

private def smartJoinMemo (p q : Nnf α) :
    StateM (Memo α) {n : Nnf α // n = smartJoin p q} := do
  let result ← smartMeetMemo p.compl q.compl
  return ⟨result.val.compl, by simp [smartJoin, result.property]⟩

/-- Reuse normal forms and internal comparisons of shared subtrees. -/
def normalizeMemo (p : Nnf α) :
    StateM (Memo α) {n : Nnf α // n = p.normalize} := do
  if (← get).config.normalization then
    if let some answer := (← get).normalForms.get? p then
      modify fun cache => { cache with stats.normalizationHits := cache.stats.normalizationHits + 1 }
      return answer
  modify fun cache => { cache with stats.normalizationMisses := cache.stats.normalizationMisses + 1 }
  let answer ← (show StateM (Memo α) {n : Nnf α // n = p.normalize} from match p with
    | .lit a s => pure ⟨.lit a s, rfl⟩
    | .bot => pure ⟨.bot, rfl⟩
    | .top => pure ⟨.top, rfl⟩
    | .meet p q => do
        let left ← normalizeMemo p
        let right ← normalizeMemo q
        let result ← smartMeetMemo left.val right.val
        pure ⟨result.val, by simp [normalize, result.property, left.property, right.property]⟩
    | .join p q => do
        let left ← normalizeMemo p
        let right ← normalizeMemo q
        let result ← smartJoinMemo left.val right.val
        pure ⟨result.val, by simp [normalize, result.property, left.property, right.property]⟩)
  if (← get).config.normalization then
    modify fun cache => { cache with normalForms := cache.normalForms.insert p answer }
  return answer

/-- Normalize both operands and compare them in the same scoped cache. -/
def checkMemo (p q : Nnf α) :
    StateM (Memo α) {b : Bool // b = checkNormalizedLe p q} := do
  let left ← normalizeMemo p
  let right ← normalizeMemo q
  let answer ← compareMemo .both left.val right.val
  return ⟨answer.val, by
    simpa only [checkNormalizedLe, structuralLe, left.property, right.property]
      using answer.property⟩

/-- Check containment with a fresh cache; retain no trees between queries. -/
def checkCachedLe (p q : Nnf α) : Bool := ((checkMemo p q).run' ∅).val

/-- Preserve positive and negative decisions of the uncached checker. -/
theorem checkCachedLe_eq (p q : Nnf α) : checkCachedLe p q = checkNormalizedLe p q :=
  ((checkMemo p q).run' ∅).property

end Lisa.Orthologic.Nnf
