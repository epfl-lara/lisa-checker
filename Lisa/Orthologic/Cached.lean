import Lisa.Orthologic.CacheKey

/-! Verified memoization for the LambdaFOL OL pipeline. Cached values include
exact agreement certificates, erased by compilation. A session is explicitly
owned by its caller; there is no global cache or hidden lifetime. -/

namespace Lisa.Orthologic.Cached
open SimpleExpr

abbrev Answer (a : α) := {b : α // b = a}

instance : Hashable SomeExpr := ⟨fun p => mixHash (hash p.1) (hash p.2)⟩

structure Config where
  preparation : Bool := true
  normalization : Bool := true
  comparison : Bool := true
  keys : Bool := true
  deriving Repr

structure Stats where
  preparationHits : Nat := 0
  preparationMisses : Nat := 0
  normalizationHits : Nat := 0
  normalizationMisses : Nat := 0
  comparisonHits : Nat := 0
  comparisonMisses : Nat := 0
  keyHits : Nat := 0
  keyMisses : Nat := 0
  deriving Repr, BEq

/-- Equality and directed, polarized implication have distinct keys. -/
inductive ComparisonKey where
  | eq (s : LSort) (p q : SimpleExpr s)
  | le (p : SimpleExpr prop) (positive : Bool) (q : SimpleExpr prop) (positive' : Bool)
  deriving DecidableEq, Hashable

def ComparisonKey.result : ComparisonKey → Bool
  | .eq _ p q => latticesEQ p q
  | .le p s q t => polarLEQ p s q t

structure Cache where
  config : Config := {}
  stats : Stats := {}
  prepared : Std.DHashMap Expr (fun p => Answer (Orthologic.prepare p)) := ∅
  normalForms : Std.DHashMap SomeExpr (fun p => Answer (computeNormalForm p.2)) := ∅
  comparisons : Std.DHashMap ComparisonKey (fun k => Answer k.result) := ∅
  terms : Std.DHashMap SomeExpr (fun p => Answer p.2.toTerm) := ∅
  orderKeys : Std.DHashMap (SimpleExpr ind) (fun p => Answer p.toTerm.erase) := ∅

instance : EmptyCollection Cache := ⟨{}⟩

private def andAnswer {a b : Bool} (x : Answer a) (next : StateM Cache (Answer b)) :
    StateM Cache (Answer (a && b)) := do
  if h : x.val = true then
    let y ← next
    return ⟨y.val, by simp [← x.property, h, y.property]⟩
  else return ⟨false, by simp [← x.property, Bool.eq_false_iff.mpr h]⟩

private def orAnswer {a b : Bool} (x : Answer a) (next : StateM Cache (Answer b)) :
    StateM Cache (Answer (a || b)) := do
  if h : x.val = true then return ⟨true, by simp [← x.property, h]⟩
  else
    let y ← next
    return ⟨y.val, by simp [← x.property, Bool.eq_false_iff.mpr h, y.property]⟩

private def allAnswers (f : α → Bool) (step : ∀ a, StateM Cache (Answer (f a))) :
    (as : List α) → StateM Cache (Answer (as.all f))
  | [] => pure ⟨true, rfl⟩
  | a :: as => do andAnswer (← step a) (allAnswers f step as)

private def anyAnswers (f : α → Bool) (step : ∀ a, StateM Cache (Answer (f a))) :
    (as : List α) → StateM Cache (Answer (as.any f))
  | [] => pure ⟨false, rfl⟩
  | a :: as => do orAnswer (← step a) (anyAnswers f step as)

private def mapAnswers (f : α → β) (step : ∀ a, StateM Cache (Answer (f a))) :
    (as : List α) → StateM Cache (Answer (as.map f))
  | [] => pure ⟨[], rfl⟩
  | a :: as => do
    let head ← step a
    let tail ← mapAnswers f step as
    return ⟨head.val :: tail.val, congrArg₂ List.cons head.property tail.property⟩

private def findAnswer (f : α → Bool) (step : ∀ a, StateM Cache (Answer (f a))) :
    (as : List α) → StateM Cache (Answer (as.find? f))
  | [] => pure ⟨none, rfl⟩
  | a :: as => do
    let head ← step a
    if h : head.val = true then
      return ⟨some a, by simp [List.find?, ← head.property, h]⟩
    else
      let tail ← findAnswer f step as
      return ⟨tail.val, by simp [List.find?, ← head.property, h, tail.property]⟩

private def foldAnswers (f : β → α → β) (step : ∀ b a, StateM Cache (Answer (f b a)))
    (b : β) : (as : List α) → StateM Cache (Answer (as.foldl f b))
  | [] => pure ⟨b, rfl⟩
  | a :: as => do
    let head ← step b a
    let tail ← foldAnswers f step head.val as
    return ⟨tail.val, tail.property.trans (congrArg (fun b => as.foldl f b) head.property)⟩

/-- Reuse the Lambda erasure needed by the original identity shortcuts. -/
def termMemo (p : SimpleExpr s) : StateM Cache (Answer p.toTerm) := do
  if (← get).config.keys then
    if let some result := (← get).terms.get? ⟨s, p⟩ then
      modify fun c => {c with stats.keyHits := c.stats.keyHits + 1}
      return result
  modify fun c => {c with stats.keyMisses := c.stats.keyMisses + 1}
  let result := ⟨p.toTerm, rfl⟩
  if (← get).config.keys then
    modify fun c => {c with terms := c.terms.insert ⟨s, p⟩ result}
  return result

private def memoCompare (key : ComparisonKey) (compute : StateM Cache (Answer key.result)) :
    StateM Cache (Answer key.result) := do
  if (← get).config.comparison then
    if let some result := (← get).comparisons.get? key then
      modify fun c => {c with stats.comparisonHits := c.stats.comparisonHits + 1}
      return result
  modify fun c => {c with stats.comparisonMisses := c.stats.comparisonMisses + 1}
  let result ← compute
  if (← get).config.comparison then
    modify fun c => {c with comparisons := c.comparisons.insert key result}
  return result

local macro "memo_decrease" hn:ident : tactic => `(tactic|
  (try simp only [SimpleExpr.size] at $hn ⊢
   omega))

local macro "member_decrease" hn:ident x:ident : tactic => `(tactic|
  (have hx := SimpleExpr.size_lt_conj (Subtype.property $x)
   simp only [SimpleExpr.size] at hx
   memo_decrease $hn))

mutual

/-- Memoized polarized implication. Each branch mirrors `polarLEQ`; the size
measure belongs only to the termination proof, not to an executable argument. -/
private def polarLEQAt (n : Nat) (p : SimpleExpr prop) (positive : Bool)
    (q : SimpleExpr prop) (positive' : Bool) (hn : 2 * (p.size + q.size) = n) :
    StateM Cache (Answer (polarLEQ p positive q positive')) := by
  have implies (p s q t) (lt : 2 * (p.size + q.size) < n) :=
    polarLEQAt (2 * (p.size + q.size)) p s q t rfl
  have equivalent {s} (p q : SimpleExpr s) (lt : 2 * (p.size + q.size) + 1 < n) :=
    latticesEQAt (2 * (p.size + q.size) + 1) p q rfl
  apply memoCompare (.le p positive q positive')
  change StateM Cache (Answer (polarLEQ p positive q positive'))
  refine do
    let left ← termMemo p
    let right ← termMemo q
    ?_
  unfold polarLEQ
  rw [← left.property, ← right.property]
  split
  · exact pure ⟨true, rfl⟩
  · split
    next p _ => -- .neg p, positive, q, positive'
      exact implies p (!positive) _ positive' (by memo_decrease hn)
    next q _ _ => -- p, positive, .neg q, positive'
      exact implies _ positive q (!positive') (by memo_decrease hn)
    · -- False implies anything.
      exact pure ⟨true, rfl⟩
    · -- Anything implies true.
      exact pure ⟨true, rfl⟩
    next a b c d _ => -- .equal a b, positive, .equal c d, positive'
      refine andAnswer ⟨positive == positive', rfl⟩ ?_
      exact do
        let forward ← andAnswer (← equivalent a c (by memo_decrease hn))
          (equivalent b d (by memo_decrease hn))
        orAnswer forward (do
          andAnswer (← equivalent a d (by memo_decrease hn)) (equivalent b c (by memo_decrease hn)))
    next p q _ => -- .all p, positive, .all q, positive'
      refine andAnswer ⟨positive == positive', rfl⟩ ?_
      split
      · exact implies p true q true (by memo_decrease hn)
      · exact implies q true p true (by memo_decrease hn)
    · -- A positive conjunction on the right requires every factor.
      exact allAnswers _ (fun q => implies _ _ _ _ (by member_decrease hn q)) _
    · -- A negative conjunction on the left requires every factor.
      exact allAnswers _ (fun p => implies _ _ _ _ (by member_decrease hn p)) _
    · -- Meet versus join: try a factor from either side.
      exact do
        let fromLeft ← anyAnswers _ (fun p => implies _ _ _ _ (by member_decrease hn p)) _
        orAnswer fromLeft (anyAnswers _ (fun q => implies _ _ _ _ (by member_decrease hn q)) _)
    · -- A negative conjunction on the right needs one factor.
      exact anyAnswers _ (fun q => implies _ _ _ _ (by member_decrease hn q)) _
    · -- A positive conjunction on the left needs one factor.
      exact anyAnswers _ (fun p => implies _ _ _ _ (by member_decrease hn p)) _
    · -- Applications require equal argument sorts and equivalent children.
      refine andAnswer ⟨_, rfl⟩ ?_
      split
      · rename_i h; cases h
        exact do
          andAnswer (← equivalent _ _ (by memo_decrease hn)) (equivalent _ _ (by memo_decrease hn))
      · exact pure ⟨false, rfl⟩
    · exact pure ⟨false, rfl⟩
termination_by n

/-- Memoized equivalence: two directions at proposition sort, constructor
congruence at the other sorts. -/
private def latticesEQAt (n : Nat) (p q : SimpleExpr s)
    (hn : 2 * (p.size + q.size) + 1 = n) : StateM Cache (Answer (latticesEQ p q)) := by
  have implies (p s q t) (lt : 2 * (p.size + q.size) < n) :=
    polarLEQAt (2 * (p.size + q.size)) p s q t rfl
  have equivalent {s} (p q : SimpleExpr s) (lt : 2 * (p.size + q.size) + 1 < n) :=
    latticesEQAt (2 * (p.size + q.size) + 1) p q rfl
  apply memoCompare (.eq s p q)
  change StateM Cache (Answer (latticesEQ p q))
  refine do
    let left ← termMemo p
    let right ← termMemo q
    ?_
  unfold latticesEQ
  rw [← left.property, ← right.property]
  split
  · exact pure ⟨true, rfl⟩
  · split
    · -- Propositions: implication in both directions.
      exact do
        andAnswer (← implies _ _ _ _ (by memo_decrease hn)) (implies _ _ _ _ (by memo_decrease hn))
    · -- Applications: same argument sort, then congruence of both children.
      split
      · rename_i h; cases h
        exact do
          andAnswer (← equivalent _ _ (by memo_decrease hn)) (equivalent _ _ (by memo_decrease hn))
      · exact pure ⟨false, rfl⟩
    · -- Lambdas: compare the bodies under the common binder.
      exact equivalent _ _ (by memo_decrease hn)
    · exact pure ⟨false, rfl⟩
termination_by n

end

/-- Recursive memoized polarized implication, including negative answers. -/
def polarLEQMemo (p : SimpleExpr prop) (s : Bool) (q : SimpleExpr prop) (t : Bool) :
    StateM Cache (Answer (polarLEQ p s q t)) :=
  polarLEQAt _ p s q t rfl

/-- Recursive memoized equivalence at any sort. -/
def latticesEQMemo (p q : SimpleExpr s) : StateM Cache (Answer (latticesEQ p q)) :=
  latticesEQAt _ p q rfl

def latticesLEQMemo (p q : SimpleExpr prop) : StateM Cache (Answer (latticesLEQ p q)) :=
  polarLEQMemo p true q true


private def refineFactorAt (n : Nat) (context : SimpleExpr prop) (positive : Bool)
    (p : SimpleExpr prop) (sign : Bool) (hn : p.size = n) :
    StateM Cache (Answer (refineFactor context positive p sign)) := by
  have child (p : SimpleExpr prop) (sign : Bool) (lt : p.size < n) :=
    refineFactorAt p.size context positive p sign rfl
  unfold refineFactor
  split
  · exact child _ _ (by memo_decrease hn)
  · rename_i ps
    refine do
      let children ← mapAnswers _
        (fun p : {p // p ∈ ps} => child p.val true (by member_decrease hn p)) ps.attach
      return ⟨children.val.flatten, by rw [children.property]; rfl⟩
  · rename_i ps
    refine do
      let found ← findAnswer (fun p : {p // p ∈ ps} =>
        if positive then polarLEQ context true p.val false else polarLEQ p.val true context false)
        (fun p => ?_) ps.attach
      ?_
    · split <;> exact polarLEQMemo _ _ _ _
    · rw [← found.property]
      cases found.val with
      | none => exact pure ⟨_, rfl⟩
      | some p => exact child p.val false (by member_decrease hn p)
  · exact pure ⟨_, rfl⟩
termination_by n

private def refineFactorMemo (context : SimpleExpr prop) (positive : Bool)
    (p : SimpleExpr prop) (sign : Bool) : StateM Cache (Answer (refineFactor context positive p sign)) :=
  refineFactorAt p.size context positive p sign rfl

private def pruneFactorsMemo (accepted : List (SimpleExpr prop)) :
    (ps : List (SimpleExpr prop)) → StateM Cache (Answer (pruneFactors accepted ps))
  | [] => pure ⟨accepted, rfl⟩
  | p :: ps => do
    let answer ← latticesLEQMemo (.conj (ps ++ accepted)) p
    if h : answer.val = true then
      let rest ← pruneFactorsMemo accepted ps
      return ⟨rest.val, by simp [pruneFactors, ← answer.property, h, rest.property]⟩
    else
      let rest ← pruneFactorsMemo (p :: accepted) ps
      return ⟨rest.val, by simp [pruneFactors, ← answer.property, h, rest.property]⟩

def reduceListMemo (ps : List (SimpleExpr prop)) (positive : Bool) :
    StateM Cache (Answer (reduceList ps positive)) := do
  let flattened ← foldAnswers (fun acc p => refineFactor (.conj ps) positive p true ++ acc)
    (fun acc p => do
      let result ← refineFactorMemo (.conj ps) positive p true
      return ⟨result.val ++ acc, by rw [result.property]⟩) [] ps
  let result ← pruneFactorsMemo [] flattened.val
  return ⟨result.val, by simp only [result.property, flattened.property, reduceList]⟩

private def contradictionMemo (ps : List (SimpleExpr prop)) (positive : Bool) :
    StateM Cache (Answer (checkForContradiction ps positive)) := by
  unfold checkForContradiction
  split <;> exact anyAnswers _ (fun _ => polarLEQMemo _ _ _ _) ps

def reduceMemo (ps : List (SimpleExpr prop)) (positive : Bool) :
    StateM Cache (Answer (reduce ps positive)) := do
  let factors ← reduceListMemo ps positive
  let contradiction ← contradictionMemo factors.val positive
  return ⟨if contradiction.val then (if positive then .neg .top else .top)
      else assemble factors.val positive, by
    simp only [reduce, ← factors.property, ← contradiction.property]⟩

/-- Cache the explicit-sort syntax used to orient symmetric equalities. -/
def orderKeyMemo (p : SimpleExpr ind) : StateM Cache (Answer p.toTerm.erase) := do
  if (← get).config.keys then
    if let some result := (← get).orderKeys.get? p then
      modify fun c => {c with stats.keyHits := c.stats.keyHits + 1}
      return result
  modify fun c => {c with stats.keyMisses := c.stats.keyMisses + 1}
  let term ← termMemo p
  let result := ⟨term.val.erase, by rw [term.property]⟩
  if (← get).config.keys then
    modify fun c => {c with orderKeys := c.orderKeys.insert p result}
  return result

private def normalizeEqualityMemo (a b : SimpleExpr ind) :
    StateM Cache (Answer (normalizeEquality a b)) := do
  let same ← latticesEQMemo a b
  if h : same.val = true then
    return ⟨.top, by simp [normalizeEquality, ← same.property, h]⟩
  else
    let left ← orderKeyMemo a
    let right ← orderKeyMemo b
    return ⟨if (StructuralOrder.compareTerms left.val right.val).isLE then .equal a b else .equal b a, by
      simp [normalizeEquality, ← same.property, h, orientEquality, left.property, right.property]⟩

private def normalFormAt (n : Nat) {s} (p : SimpleExpr s) (hn : p.size = n) :
    StateM Cache (Answer (computeNormalForm p)) := by
  have child {s} (p : SimpleExpr s) (lt : p.size < n) := normalFormAt p.size p rfl
  refine do
    if (← get).config.normalization then
      if let some result := (← get).normalForms.get? ⟨s, p⟩ then
        modify fun c => {c with stats.normalizationHits := c.stats.normalizationHits + 1}
        return result
    modify fun c => {c with stats.normalizationMisses := c.stats.normalizationMisses + 1}
    let result ← ?_
    if (← get).config.normalization then
      modify fun c => {c with normalForms := c.normalForms.insert ⟨s, p⟩ result}
    return result
  unfold computeNormalForm
  split
  · exact pure ⟨_, rfl⟩
  · exact pure ⟨_, rfl⟩
  · exact pure ⟨_, rfl⟩
  · rename_i a f
    exact do
      let f ← child f (by memo_decrease hn)
      let a ← child a (by memo_decrease hn)
      return ⟨.app f.val a.val, by rw [f.property, a.property]⟩
  · rename_i b
    exact do
      let b ← child b (by memo_decrease hn)
      return ⟨.lam _ b.val, by rw [b.property]⟩
  · exact pure ⟨_, rfl⟩
  · rename_i ps
    exact do
      let ps ← mapAnswers _
        (fun p : {p // p ∈ ps} => child p.val (by member_decrease hn p)) ps.attach
      let result ← reduceMemo ps.val true
      return ⟨result.val, by rw [result.property, ps.property]⟩
  · rename_i ps
    exact do
      let ps ← mapAnswers _
        (fun p : {p // p ∈ ps} => child p.val (by member_decrease hn p)) ps.attach
      let result ← reduceMemo ps.val false
      return ⟨result.val, by rw [result.property, ps.property]⟩
  · rename_i b _
    exact do
      let b ← child b (by memo_decrease hn)
      return ⟨inverse b.val, by rw [b.property]⟩
  · rename_i b
    exact do
      let b ← child b (by memo_decrease hn)
      return ⟨normalizeAll b.val, by rw [b.property]⟩
  · rename_i a b
    exact do
      let a ← child a (by memo_decrease hn)
      let b ← child b (by memo_decrease hn)
      let result ← normalizeEqualityMemo a.val b.val
      return ⟨result.val, by rw [result.property, a.property, b.property]⟩
termination_by n

/-- Cache each normalized subtree; internal refinement and pruning use the same
comparison cache as public queries. The size parameter above only justifies
termination; it is never fuel and cannot exhaust. -/
def computeNormalFormMemo (p : SimpleExpr s) : StateM Cache (Answer (computeNormalForm p)) :=
  normalFormAt p.size p rfl

/-- Reuse elaboration, alpha-beta-eta canonicalization and OL normalization for
identical named inputs. Malformed-input results are cached as well. -/
def prepareMemo (p : Expr) : StateM Cache (Answer (Orthologic.prepare p)) := by
  refine do
    if (← get).config.preparation then
      if let some result := (← get).prepared.get? p then
        modify fun c => {c with stats.preparationHits := c.stats.preparationHits + 1}
        return result
    modify fun c => {c with stats.preparationMisses := c.stats.preparationMisses + 1}
    let result ← ?_
    if (← get).config.preparation then
      modify fun c => {c with prepared := c.prepared.insert p result}
    return result
  cases he : Lambda.interpretNamed p Lambda.Names.free with
  | none => exact pure ⟨none, by simp [Orthologic.prepare, he]⟩
  | some e =>
    obtain ⟨s, e⟩ := e
    exact do
      let result ← computeNormalFormMemo (SimpleExpr.ofTerm (Lambda.normalize e))
      return ⟨some ⟨s, result.val⟩, by simp [Orthologic.prepare, he, result.property]⟩

def normalizeMemo (p : Expr) : StateM Cache (Answer (Orthologic.normalize p)) := by
  refine do
    let prepared ← prepareMemo p
    ?_
  unfold Orthologic.normalize
  rw [← prepared.property]
  cases prepared.val with
  | none => exact pure ⟨none, rfl⟩
  | some e =>
    obtain ⟨s, e⟩ := e
    exact do
      let term ← termMemo e
      return ⟨some (term.val.reify Lambda.Context.empty), by rw [term.property]; rfl⟩

def isSameMemo (p q : Expr) : StateM Cache (Answer (Orthologic.isSame p q)) := by
  refine do
    let left ← prepareMemo p
    ?_
  unfold Orthologic.isSame
  rw [← left.property]
  cases left.val with
  | none => exact pure ⟨none, rfl⟩
  | some e =>
    obtain ⟨s, e⟩ := e
    refine do
      let right ← prepareMemo q
      ?_
    rw [← right.property]
    cases right.val with
    | none => exact pure ⟨none, rfl⟩
    | some f =>
      obtain ⟨t, f⟩ := f
      by_cases hs : t = s
      · subst t
        exact do
          let result ← latticesEQMemo e f
          return ⟨some result.val, by simp [result.property]⟩
      · exact pure ⟨some false, by simp [hs]⟩

def isImplyingMemo (p q : Expr) : StateM Cache (Answer (Orthologic.isImplying p q)) := by
  refine do
    let left ← prepareMemo p
    ?_
  unfold Orthologic.isImplying
  rw [← left.property]
  cases left.val with
  | none => exact pure ⟨none, rfl⟩
  | some e =>
    obtain ⟨s, e⟩ := e
    cases s
    case ind => exact pure ⟨none, rfl⟩
    case arrow => exact pure ⟨none, rfl⟩
    case prop =>
      refine do
        let right ← prepareMemo q
        ?_
      rw [← right.property]
      cases right.val with
      | none => exact pure ⟨none, rfl⟩
      | some f =>
        obtain ⟨t, f⟩ := f
        cases t
        case ind => exact pure ⟨none, rfl⟩
        case arrow => exact pure ⟨none, rfl⟩
        case prop => exact do
          let result ← latticesLEQMemo e f
          return ⟨some result.val, by simp [result.property]⟩

/-- Convenience entry points start fresh. Use the `Memo` operations and keep
the returned `Cache` to share work across multiple queries. -/
def normalize (p : Expr) (config : Config := {}) : Option Expr :=
  ((normalizeMemo p).run' {config}).val

def isSame (p q : Expr) (config : Config := {}) : Option Bool :=
  ((isSameMemo p q).run' {config}).val

def isImplying (p q : Expr) (config : Config := {}) : Option Bool :=
  ((isImplyingMemo p q).run' {config}).val

theorem normalize_eq (p : Expr) (config : Config := {}) :
    normalize p config = Orthologic.normalize p := ((normalizeMemo p).run' {config}).property

theorem isSame_eq (p q : Expr) (config : Config := {}) :
    isSame p q config = Orthologic.isSame p q := ((isSameMemo p q).run' {config}).property

theorem isImplying_eq (p q : Expr) (config : Config := {}) :
    isImplying p q config = Orthologic.isImplying p q := ((isImplyingMemo p q).run' {config}).property

-- These results quantify over every cache, not just a cache reachable from empty.
theorem prepareMemo_eq (p : Expr) (cache : Cache) :
    ((prepareMemo p).run' cache).val = Orthologic.prepare p := ((prepareMemo p).run' cache).property

theorem normalizeMemo_eq (p : Expr) (cache : Cache) :
    ((normalizeMemo p).run' cache).val = Orthologic.normalize p := ((normalizeMemo p).run' cache).property

theorem isSameMemo_eq (p q : Expr) (cache : Cache) :
    ((isSameMemo p q).run' cache).val = Orthologic.isSame p q := ((isSameMemo p q).run' cache).property

theorem isImplyingMemo_eq (p q : Expr) (cache : Cache) :
    ((isImplyingMemo p q).run' cache).val = Orthologic.isImplying p q :=
  ((isImplyingMemo p q).run' cache).property

end Lisa.Orthologic.Cached
