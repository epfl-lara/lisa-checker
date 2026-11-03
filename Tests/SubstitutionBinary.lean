import Lisa.Checker.Binary

/-! A small independent fixture writer for the rules used in substitution tests.
It writes both streams, so the tests exercise tree decoding, step decoding and
proof checking. It is not a general-purpose proof exporter. -/
namespace SubstitutionBinary
open Lisa Expr Imported.Checker Imported.Binary

private def be (width n : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (n / 256 ^ (width - i - 1) % 256)

private def int (n : Int) : List UInt8 :=
  be 4 (if n < 0 then (n + 4294967296).toNat else n.toNat)

-- Fixture strings contain only non-NUL BMP characters, for which UTF-8 and
-- Java modified UTF-8 agree. The general string decoder is tested in Binary.
private def text (s : String) : List UInt8 :=
  be 2 s.utf8ByteSize ++ s.toUTF8.data.toList

private def sortText : LSort → String
  | .ind => "T"
  | .prop => "F"
  | .arrow a b => ">" ++ sortText a ++ sortText b

private structure Table where
  trees : Array Expr := #[]
  bytes : List UInt8 := []

private abbrev Write := StateT Table (Except String)

private def add (e : Expr) (bytes : List UInt8) : Write Nat := do
  let table ← get
  let index := table.trees.toList.idxOf e
  if index < table.trees.size then return index
  set ({ trees := table.trees.push e, bytes := table.bytes ++ bytes } : Table)
  return table.trees.size

private def writeVariable (x : SVar) : Write Nat :=
  add (.var x) ([0] ++ text x.id.name ++ be 4 x.id.idx ++ text (sortText x.sort))

private def expr : Expr → Write Nat
  | .var x => writeVariable x
  | .const c => do
    let name ← match c.id.name with
      | "top" => pure "⊤" | "bot" => pure "⊥" | "not" => pure "¬"
      | "and" => pure "∧" | "or" => pure "∨" | "imp" => pure "⇒"
      | "iff" => pure "⇔" | "eq" => pure "=" | "forall" => pure "∀"
      | "exists" => pure "∃" | "epsilon" => pure "ε"
      | name =>
        if name.startsWith "user:" then pure (name.drop 5).toString
        else throw s!"Fixture constant must use the decoded user: prefix: {name}"
    add (.const c) ([1] ++ text name ++ be 4 c.id.idx ++ text (sortText c.sort))
  | .app f a => do
    let f' ← expr f
    let a' ← expr a
    add (.app f a) ([3] ++ be 4 f' ++ be 4 a')
  | .lam x b => do
    let x' ← writeVariable x
    let b' ← expr b
    add (.lam x b) ([2] ++ be 4 x' ++ be 4 b')

private def expressions (es : List Expr) : Write (List UInt8) := do
  return be 2 es.length ++ (← es.mapM expr).flatMap (be 4)

private def statement (s : Statement) : Write (List UInt8) := do
  let pre ← expressions s.pre
  return pre ++ (← expressions s.post)

private def substitution (r : SubstRule) : Write (List UInt8) := do
  let mut bytes := be 2 r.comparisons.length
  for (pair, args) in r.comparisons do
    let source ← expr pair.source
    let target ← expr pair.target
    bytes := bytes ++ be 4 source ++ be 4 target ++ (← expressions (args.map Expr.var))
  let params ← expressions (r.context.params.map Expr.var)
  return bytes ++ params ++ be 4 (← expr r.context.body)

private def step (s : Step) : Write (List UInt8) := do
  let output ← statement s.statement
  match s.rule with
  | .assume => return [30] ++ output
  | .hypothesis e => return [2] ++ output ++ be 4 (← expr e)
  | .restateTrue => return [1] ++ output
  | .leftSubst p q r => return [33] ++ output ++ int p ++ int q ++ (← substitution r)
  | .rightSubst p q r => return [34] ++ output ++ int p ++ int q ++ (← substitution r)
  | rule => throw s!"Unsupported fixture rule: {rule.name}"

def encode (proof : LinearProof) (imports : Array Statement := #[]) :
    Except String (ByteArray × ByteArray) := do
  let write : Write (List UInt8) := do
    let external ← imports.toList.mapM statement
    let steps ← proof.toList.mapM step
    return be 2 1 ++ text "substitution" ++ be 2 0 ++
      be 4 imports.size ++ external.flatten ++ be 4 proof.size ++ steps.flatten
  let (bytes, table) ← write.run {}
  return (ByteArray.mk table.bytes.toArray, ByteArray.mk bytes.toArray)

def reader (bytes : ByteArray) (page : Nat) : IO Reader := do
  let position ← IO.mkRef 0
  Reader.create fun requested => do
    let start ← position.get
    let stop := min bytes.size (start + min requested page)
    position.set stop
    return bytes.extract start stop

def check (proof : LinearProof) (page : Nat := 65536) (imports : Array Statement := #[]) :
    IO (Except DecodeError (Array (NamedProof ProofRelation))) := do
  let (trees, bytes) ← IO.ofExcept (encode proof imports)
  let treeReader ← reader trees page
  match ← (readTrees.run treeReader).run with
  | .error e => return .error e
  | .ok trees =>
    let proofReader ← reader bytes page
    (readBundle trees |>.run proofReader).run

end SubstitutionBinary
