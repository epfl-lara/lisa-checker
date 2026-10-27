import Lisa.Checker.Check
import Lisa.Checker.Display

open Lisa Expr Imported.Checker

namespace Imported.Binary

structure DecodeError where
  offset : Nat
  message : String
deriving Repr

private structure Cursor where
  bytes : ByteArray := ByteArray.empty
  position : Nat := 0
  offset : Nat := 0

/-- Read bounded chunks; retain only the current byte page. -/
structure Reader where
  readChunk : Nat → IO ByteArray
  private cursor : IO.Ref Cursor

def Reader.create (readChunk : Nat → IO ByteArray) : IO Reader := do
  return ⟨readChunk, ← IO.mkRef {}⟩

abbrev DecodeM := ReaderT Reader (ExceptT DecodeError IO)

private def fail (message : String) : DecodeM α := do
  let reader ← read
  let cursor ← reader.cursor.get
  throw ⟨cursor.offset, message⟩

private def byte? : DecodeM (Option UInt8) := do
  let reader ← read
  let mut cursor ← reader.cursor.get
  if cursor.position = cursor.bytes.size then
    let chunk ← reader.readChunk 65536
    if chunk.isEmpty then return none
    cursor := { cursor with bytes := chunk, position := 0 }
  let value := cursor.bytes[cursor.position]!
  reader.cursor.set { cursor with position := cursor.position + 1, offset := cursor.offset + 1 }
  return some value

private def byte : DecodeM UInt8 := do
  match ← byte? with
  | some b => return b
  | none => fail "Unexpected end of stream"

private def unsigned (count : Nat) : DecodeM Nat := do
  let mut result := 0
  for _ in [:count] do result := result * 256 + (← byte).toNat
  return result

private def integer : DecodeM Int := do
  let n ← unsigned 4
  return if n < 2147483648 then Int.ofNat n else Int.ofNat n - 4294967296

private def count32 : DecodeM Nat := do
  let n ← integer
  if n < 0 then fail "Negative record count or identifier index" else return n.toNat

private def count16 : DecodeM Nat := do
  let n ← unsigned 2
  if n > 32767 then fail "Negative short count" else return n

private def many (n : Nat) (item : DecodeM α) : DecodeM (List α) := do
  let mut result := []
  for _ in [:n] do result := (← item) :: result
  return result.reverse

/-- Decode Java's modified UTF-8, including UTF-16 surrogate pairs. -/
private def utf : DecodeM String := do
  let size ← unsigned 2
  let bytes ← many size byte
  let mut units : Array Nat := #[]
  let data := bytes.toArray
  let mut i := 0
  while i < data.size do
    let b := data[i]!.toNat
    if b < 128 then
      units := units.push b
      i := i + 1
    else if b ≥ 192 && b < 224 then
      if i + 1 ≥ data.size then fail "Truncated modified UTF-8"
      let c := data[i + 1]!.toNat
      if c < 128 || c ≥ 192 then fail "Invalid modified UTF-8 continuation"
      let unit := (b - 192) * 64 + c - 128
      if unit < 128 && unit ≠ 0 then fail "Overlong modified UTF-8"
      units := units.push unit
      i := i + 2
    else if b ≥ 224 && b < 240 then
      if i + 2 ≥ data.size then fail "Truncated modified UTF-8"
      let c := data[i + 1]!.toNat
      let d := data[i + 2]!.toNat
      if c < 128 || c ≥ 192 || d < 128 || d ≥ 192 then
        fail "Invalid modified UTF-8 continuation"
      let unit := (b - 224) * 4096 + (c - 128) * 64 + d - 128
      if unit < 2048 then fail "Overlong modified UTF-8"
      units := units.push unit
      i := i + 3
    else fail "Invalid modified UTF-8 lead byte"
  let mut chars := []
  i := 0
  while i < units.size do
    let unit := units[i]!
    if unit ≥ 55296 && unit < 56320 then
      if i + 1 ≥ units.size then fail "Unpaired UTF-16 high surrogate"
      let low := units[i + 1]!
      if low < 56320 || low ≥ 57344 then fail "Unpaired UTF-16 high surrogate"
      chars := Char.ofNat (65536 + (unit - 55296) * 1024 + low - 56320) :: chars
      i := i + 2
    else if unit ≥ 56320 && unit < 57344 then
      fail "Unpaired UTF-16 low surrogate"
    else
      chars := Char.ofNat unit :: chars
      i := i + 1
  return String.ofList chars.reverse

private def parseSort : Nat → List Char → Except String (LSort × List Char)
  | 0, _ => .error "Invalid sort"
  | _ + 1, 'T' :: rest => .ok (ind, rest)
  | _ + 1, 'F' :: rest => .ok (prop, rest)
  | fuel + 1, '>' :: rest => do
    let (domain, rest) ← parseSort fuel rest
    let (codomain, rest) ← parseSort fuel rest
    return (domain >> codomain, rest)
  | _, _ => .error "Invalid sort"

private def sort : DecodeM LSort := do
  let text ← utf
  match parseSort text.length text.toList with
  | .ok (s, []) => return s
  | _ => fail "Invalid or trailing sort encoding"

/-- Separate user constants from the fixed logical signature. -/
private def constant (id : Identifier) (s : LSort) : SConst :=
  let logical :=
    if id.idx ≠ 0 then none
    else match id.name, s with
    | "⊤", .prop => some "top"
    | "⊥", .prop => some "bot"
    | "¬", .arrow .prop .prop => some "not"
    | "⇒", .arrow .prop (.arrow .prop .prop) => some "imp"
    | "⇔", .arrow .prop (.arrow .prop .prop) => some "iff"
    | "∧", .arrow .prop (.arrow .prop .prop) => some "and"
    | "∨", .arrow .prop (.arrow .prop .prop) => some "or"
    | "=", .arrow .ind (.arrow .ind .prop) => some "eq"
    | "∀", .arrow (.arrow .ind .prop) .prop => some "forall"
    | "∃", .arrow (.arrow .ind .prop) .prop => some "exists"
    | "ε", .arrow (.arrow .ind .prop) .ind => some "epsilon"
    | _, _ => none
  match logical with
  | some name => .named name s
  | none => ⟨{ id with name := "user:" ++ id.name }, s⟩

private def expression (trees : Array Expr) : DecodeM Expr := do
  let index ← integer
  if index < 0 then fail "Negative expression reference"
  match trees[index.toNat]? with
  | some e => return e
  | none => fail s!"Invalid expression reference {index}"

private def readVariable (trees : Array Expr) : DecodeM SVar := do
  match ← expression trees with
  | .var x => return x
  | _ => fail "Expected readVariable tree"

/-- Read the shared tree table; reject forward references and malformed entries. -/
def readTrees : DecodeM (Array Expr) := do
  let mut trees := #[]
  while true do
    let some tag ← byte? | return trees
    let e : Expr ← (match tag.toNat with
    | 0 => do
      let name ← utf
      let index ← count32
      return Expr.var ⟨⟨name, index⟩, ← sort⟩
    | 1 => do
      let name ← utf
      let index ← count32
      return Expr.const (constant ⟨name, index⟩ (← sort))
    | 2 => return Expr.lam (← readVariable trees) (← expression trees)
    | 3 => return Expr.app (← expression trees) (← expression trees)
    | _ => fail s!"Invalid expression tag {tag}")
    if e.sort.isNone then fail "Ill-sorted expression tree"
    trees := trees.push e
  return trees

private def statement (trees : Array Expr) : DecodeM Statement := do
  let pre ← many (← count16) (expression trees)
  let post ← many (← count16) (expression trees)
  return ⟨pre, post⟩

private def equality (trees : Array Expr) : DecodeM (Expr × Expr) := do
  match ← expression trees with
  | .app (.app (.const c) s) t =>
    if c = SConst.named "eq" (ind >> ind >> prop) then return (s, t)
    else fail "Expected equality formula"
  | _ => fail "Expected equality formula"

/-- Decode a step without trusting its declared conclusion or references. -/
def readStep (trees : Array Expr) : DecodeM Step := do
  let tag ← byte
  if tag.toNat = 24 || tag.toNat = 25 then
    fail s!"Unsupported legacy substitution tag {tag}; two-premise substitution requires an updated export format"
  if [11, 21, 27, 28, 29, 32].contains tag.toNat then
    fail s!"Unsupported or trusted proof-step tag {tag}"
  let output ← statement trees
  let rule : Rule ← (match tag.toNat with
  | 0 => return Rule.restate (← integer)
  | 1 => return Rule.restateTrue
  | 2 => return Rule.hypothesis (← expression trees)
  | 3 => return Rule.cut (← integer) (← integer) (← expression trees)
  | 4 => return Rule.leftAnd (← integer) (← expression trees) (← expression trees)
  | 5 | 12 => do
    let refs ← many (← count16) integer
    let formulas ← many (← count16) (expression trees)
    if refs.length ≠ formulas.length then fail "Mismatched n-ary premise and formula counts"
    return if tag.toNat = 5 then .leftOr (refs.zip formulas) else .rightAnd (refs.zip formulas)
  | 6 => return Rule.leftImp (← integer) (← integer) (← expression trees) (← expression trees)
  | 7 => return Rule.leftIff (← integer) (← expression trees) (← expression trees)
  | 8 => return Rule.leftNot (← integer) (← expression trees)
  | 9 | 18 | 19 => do
    let ref ← integer
    let φ ← expression trees
    let x ← readVariable trees
    let t ← expression trees
    return if tag.toNat = 9 then .leftForall ref x φ t
      else if tag.toNat = 18 then .rightExists ref x φ t else .rightEpsilon ref x φ t
  | 10 | 17 => do
    let ref ← integer
    let φ ← expression trees
    let x ← readVariable trees
    return if tag.toNat = 10 then .leftExists ref x φ else .rightForall ref x φ
  | 13 => return Rule.rightOr (← integer) (← expression trees) (← expression trees)
  | 14 => return Rule.rightImp (← integer) (← expression trees) (← expression trees)
  | 15 => return Rule.rightIff (← integer) (← integer) (← expression trees) (← expression trees)
  | 16 => return Rule.rightNot (← integer) (← expression trees)
  | 20 => return Rule.weakening (← integer)
  | 22 => do
    let ref ← integer
    let (s, t) ← equality trees
    return Rule.leftRefl ref s t
  | 23 => do
    let (s, t) ← equality trees
    return Rule.rightRefl s t
  | 26 => do
    let ref ← integer
    let pairs : List (SVar × Expr) ← many (← count16) do return (← readVariable trees, ← expression trees)
    return Rule.instSchema ref (pairs.foldl (fun σ (x, e) => σ.insert x e) .nil)
  | 30 => return Rule.assume
  | 31 => return Rule.discharge (← integer) (← integer)
  | _ => fail s!"Invalid proof-step tag {tag}")
  return ⟨output, rule⟩

variable {leq : ExprRel} [CheckerOrder leq]

/-- Retain declared counts alongside the checked result. -/
structure ProofRecord (leq : ExprRel) where
  checked : Checked leq
  steps : Nat
  imports : Nat

/-- Check records as they arrive; retain checked premise metadata and declared counts. -/
def readProofRecord (trees : Array Expr) (diagnostics := false)
    (matching : Matching leq := .exact leq) : DecodeM (ProofRecord leq) := do
  let external ← many (← count32) (statement trees)
  let mut imports := #[]
  for s in external do
    match checkStepFallback matching #[] #[] ⟨s, .assume⟩ with
    | .ok result => imports := imports.push result
    | .error e => fail s!"Invalid import: {repr e}"
  let size ← count32
  let mut checked := #[]
  for i in [:size] do
    let step ← readStep trees
    if diagnostics then
      liftM (IO.eprintln s!"Checking step {i} ({step.rule.name}, refs {step.rule.references}): {step.statement.display}")
    match checkStepFallback matching imports checked step with
    | .ok result => checked := checked.push result
    | .error e =>
      if diagnostics then
        liftM (IO.eprintln s!"Step {i} ({step.rule.name}) conclusion: {step.statement.display}")
        for ref in step.rule.references do
          match lookup imports checked ref with
          | .ok premise => liftM (IO.eprintln s!"Premise {ref}: {premise.statement.display}")
          | .error _ => pure ()
      fail s!"Invalid step {i} ({step.rule.name}): {repr e}"
  match checked.back? with
  | some result => return ⟨result, size, external.length⟩
  | none => fail "Empty proof"

/-- Check a proof stream and return its actual final conclusion and certificate. -/
def readProof (trees : Array Expr) (matching : Matching leq := .exact leq) : DecodeM (Checked leq) := do
  return (← readProofRecord trees false matching).checked

structure NamedProof (leq : ExprRel) where
  name : String
  justifications : List String
  checked : Checked leq
  steps : Nat
  imports : Nat

/-- Check a named bundle relative to its explicit imports and reject trailing bytes. -/
def readBundle (trees : Array Expr) (diagnostics := false)
    (matching : Matching leq := .exact leq) : DecodeM (Array (NamedProof leq)) := do
  let size ← count16
  if size = 0 then fail "Empty proof bundle"
  let mut results := #[]
  for _ in [:size] do
    let name ← utf
    let justifications ← many (← count16) utf
    let proof ← readProofRecord trees diagnostics matching
    results := results.push ⟨name, justifications, proof.checked, proof.steps, proof.imports⟩
  if (← byte?).isSome then fail "Trailing data after proof bundle"
  return results

/-- Open paired binary streams and check a bundle relative to its declared imports. -/
def checkFiles (treePath proofPath : System.FilePath) (diagnostics := false)
    (matching : Matching leq := .exact leq) :
    IO (Except DecodeError (Array (NamedProof leq))) :=
  IO.FS.withFile treePath .read fun treeHandle =>
  IO.FS.withFile proofPath .read fun proofHandle => do
    let treeReader ← Reader.create (fun n => treeHandle.read n.toUSize)
    match ← ((readTrees).run treeReader).run with
    | .error e => return .error { e with message := "trees: " ++ e.message }
    | .ok trees =>
      let proofReader ← Reader.create (fun n => proofHandle.read n.toUSize)
      return (← ((readBundle (leq := leq) trees diagnostics matching).run proofReader).run).mapError
        fun e => { e with message := "proof: " ++ e.message }

end Imported.Binary
