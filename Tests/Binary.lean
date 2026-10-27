import Lisa.Checker.Binary

open Lisa Expr Imported.Checker Imported.Binary

-- Encode fixed protocol fixtures independently of the decoder.
private def be (width n : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (n / 256 ^ (width - i - 1) % 256)
private def text (s : String) : List UInt8 :=
  be 2 s.utf8ByteSize ++ s.toUTF8.data.toList
private def constEntry (name ty : String) : List UInt8 :=
  [1] ++ text name ++ be 4 0 ++ text ty
private def seq (pre post : List Nat) : List UInt8 :=
  be 2 pre.length ++ pre.flatMap (be 4) ++ be 2 post.length ++ post.flatMap (be 4)
private def trees : List UInt8 :=
  constEntry "A" "F" ++ constEntry "⇒" ">F>FF" ++
    [3] ++ be 4 1 ++ be 4 0 ++ [3] ++ be 4 2 ++ be 4 0
private def header (steps : Nat) : List UInt8 :=
  be 2 1 ++ text "identity" ++ be 2 0 ++ be 4 0 ++ be 4 steps
private def proof : List UInt8 :=
  header 2 ++ [2] ++ seq [0] [0] ++ be 4 0 ++
    [14] ++ seq [] [3] ++ be 4 0 ++ be 4 0 ++ be 4 0

private def reader (bytes : List UInt8) (chunkSize : Nat := 65536) : IO Reader := do
  let data := ByteArray.mk bytes.toArray
  let position ← IO.mkRef 0
  Reader.create fun requested => do
    let start ← position.get
    let stop := min data.size (start + min requested chunkSize)
    position.set stop
    return data.extract start stop

private def run
    (treeBytes proofBytes : List UInt8) (chunkSize : Nat := 65536) :
    IO (Except DecodeError (Array (NamedProof ProofRelation))) := do
  let treeReader ← reader treeBytes chunkSize
  match ← (readTrees.run treeReader).run with
  | .error e => return .error e
  | .ok table =>
    let proofReader ← reader proofBytes chunkSize
    (readBundle table |>.run proofReader).run

private def rejected (name : String) (treeBytes proofBytes : List UInt8) : IO Unit := do
  match ← run treeBytes proofBytes with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{name}: accepted invalid stream")

#eval show IO Unit from do
  for chunkSize in [1, 2, 7, 65536] do
    match ← run trees proof chunkSize with
    | .error e => throw (IO.userError s!"identity: {repr e}")
    | .ok results =>
      let some result := results[0]? | throw (IO.userError "empty checked bundle")
      unless results.size = 1 && result.name = "identity" do
        throw (IO.userError "wrong bundle metadata")
      unless result.checked.assumptions = ∅ do
        throw (IO.userError "closed fixture retained assumptions")
  -- Every tree is used: any proper prefix fails decoding or proof lookup.
  for n in [:trees.length] do rejected s!"tree truncation {n}" (trees.take n) proof
  for n in [:proof.length] do rejected s!"proof truncation {n}" trees (proof.take n)
  rejected "trailing proof bytes" trees (proof ++ [0])
  rejected "unknown tree tag" [255] proof
  rejected "forward tree reference" ([3] ++ be 4 0 ++ be 4 0) proof
  rejected "lambda binder is not variable"
    (constEntry "A" "F" ++ [2] ++ be 4 0 ++ be 4 0) proof
  rejected "ill-sorted application"
    (constEntry "A" "F" ++ [3] ++ be 4 0 ++ be 4 0) proof
  rejected "invalid sort" (constEntry "A" "Fgarbage") proof
  rejected "negative identifier"
    ([1] ++ text "A" ++ be 4 4294967295 ++ text "F") proof
  rejected "negative sequent size" trees (header 1 ++ [2] ++ be 2 65535)
  rejected "negative import count" trees
    (be 2 1 ++ text "bad" ++ be 2 0 ++ be 4 4294967295)
  rejected "forward step reference" trees
    (header 1 ++ [0] ++ seq [0] [0] ++ be 4 0)
  rejected "undeclared import" trees
    (header 1 ++ [0] ++ seq [0] [0] ++ be 4 4294967295)
  rejected "mismatched n-ary lengths" trees
    (header 1 ++ [5] ++ seq [0] [0] ++ be 2 1 ++ be 4 0 ++ be 2 0)
  for tag in [11, 21, 24, 25, 27, 28, 29, 32, 255] do
    rejected s!"unsupported tag {tag}" trees (header 1 ++ [UInt8.ofNat tag] ++ seq [] [])
  -- Modified UTF-8 encodes NUL as C0 80 and supplementary scalars as two surrogates.
  let name := [0xC0, 0x80, 0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80]
  let unicodeProof := be 2 1 ++ be 2 name.length ++ name ++ be 2 0 ++ be 4 0 ++
    be 4 1 ++ [1] ++ seq [] [3]
  match ← run trees unicodeProof 1 with
  | .error e => throw (IO.userError s!"modified UTF-8 rejected: {repr e}")
  | .ok results =>
    let some result := results[0]? | throw (IO.userError "empty Unicode bundle")
    unless result.name = String.ofList [Char.ofNat 0, '😀'] do
      throw (IO.userError "modified UTF-8 decoded incorrectly")
  rejected "unpaired surrogate" trees
    (be 2 1 ++ be 2 3 ++ [0xED, 0xA0, 0xBD])
  rejected "UTF-8 four-byte form is not modified UTF-8" trees
    (be 2 1 ++ be 2 4 ++ [0xF0, 0x9F, 0x98, 0x80])

#print axioms Imported.Binary.readProof
#print axioms Imported.Binary.readBundle

private def ruleTag : Rule → Option Nat
  | .assume => some 30
  | .discharge .. => some 31
  | .restate .. => some 0
  | .weakening .. => some 20
  | .restateTrue => some 1
  | .hypothesis .. => some 2
  | .cut .. => some 3
  | .leftAnd .. => some 4
  | .leftOr .. => some 5
  | .leftImp .. => some 6
  | .leftIff .. => some 7
  | .leftNot .. => some 8
  | .leftForall .. => some 9
  | .leftExists .. => some 10
  | .rightAnd .. => some 12
  | .rightOr .. => some 13
  | .rightImp .. => some 14
  | .rightIff .. => some 15
  | .rightNot .. => some 16
  | .rightForall .. => some 17
  | .rightExists .. => some 18
  | .rightEpsilon .. => some 19
  | .leftRefl .. => some 22
  | .rightRefl .. => some 23
  | .instSchema .. => some 26
  | .leftSubst .. => some 33
  | .rightSubst .. => some 34

-- Decode each payload layout followed by a sentinel, detecting under/over-consumption.
#eval show IO Unit from do
  let extra :=
    [0] ++ text "x" ++ be 4 0 ++ text "T" ++
    [0] ++ text "P" ++ be 4 0 ++ text "F" ++
    constEntry "=" ">T>TF" ++ constEntry "t" "T" ++
    [3] ++ be 4 6 ++ be 4 7 ++ [3] ++ be 4 8 ++ be 4 7
  let treeReader ← reader (trees ++ extra) 2
  let .ok table ← (readTrees.run treeReader).run
    | throw (IO.userError "opcode fixture tree rejected")
  let refs (xs : List Nat) := xs.flatMap (be 4)
  let nary := be 2 1 ++ be 4 0 ++ be 2 1 ++ be 4 0
  let subst := refs [0, 1] ++ be 2 1 ++ refs [7, 7] ++ be 2 0 ++
    be 2 1 ++ refs [4, 9]
  let payloads : List (Nat × List UInt8) := [
    (0, refs [0]), (1, []), (2, refs [0]), (3, refs [0, 1, 0]),
    (4, refs [0, 0, 3]), (5, nary), (6, refs [0, 1, 0, 3]),
    (7, refs [0, 0, 3]), (8, refs [0, 0]), (9, refs [0, 0, 4, 7]),
    (10, refs [0, 0, 4]), (12, nary), (13, refs [0, 0, 3]),
    (14, refs [0, 0, 3]), (15, refs [0, 1, 0, 3]), (16, refs [0, 0]),
    (17, refs [0, 0, 4]), (18, refs [0, 0, 4, 7]), (19, refs [0, 0, 4, 7]),
    (20, refs [0]), (22, refs [0, 9]), (23, refs [9]),
    (26, be 4 0 ++ be 2 1 ++ refs [5, 0]),
    (30, []), (31, refs [0, 1]), (33, subst), (34, subst)]
  for (tag, payload) in payloads do
    let bytes := [UInt8.ofNat tag] ++ seq [0] [0] ++ payload ++
      [2] ++ seq [0] [0] ++ be 4 0
    let input ← reader bytes 1
    let action := do
      let first ← readStep table
      let second ← readStep table
      return (ruleTag first.rule, ruleTag second.rule)
    match ← (action.run input).run with
    | .error e => throw (IO.userError s!"opcode {tag}: {repr e}")
    | .ok (first, second) =>
      unless first = some tag && second = some 2 do
        throw (IO.userError s!"wrong opcode layout {tag}")

-- Fixed substitution payloads check the complete field order independently of
-- the fixture writer, and reject every truncated prefix or invalid tree reference.
#eval show IO Unit from do
  let x : SVar := ⟨⟨"x", 0⟩, ind⟩
  let y : SVar := ⟨⟨"y", 0⟩, ind⟩
  let p : SVar := ⟨⟨"p", 0⟩, prop⟩
  let f : SVar := ⟨⟨"f", 0⟩, ind >> ind⟩
  let q : SVar := ⟨⟨"q", 0⟩, prop⟩
  let body := and (eq (.app (.var f) (.var x)) (.var x)) (.var q)
  let table := #[Expr.var x, .var y, .var p, top, .var f,
    .lam x (.var x), .lam y (.var y), .var q, body]
  -- Two pairs: function equality with one argument, then propositional
  -- equivalence with no arguments. The premise references are signed.
  let payload := be 4 4294967295 ++ be 4 7 ++ be 2 2 ++
    be 4 5 ++ be 4 6 ++ be 2 1 ++ be 4 1 ++
    be 4 2 ++ be 4 3 ++ be 2 0 ++ be 2 2 ++ be 4 4 ++ be 4 7 ++ be 4 8
  let snapshot (r : SubstRule) :=
    (r.comparisons.map (fun (pair, xs) => (pair.source, pair.target, xs)),
      r.context.params, r.context.body)
  let expected : SubstRule :=
    ⟨[(⟨.lam x (.var x), .lam y (.var y)⟩, [y]), (⟨.var p, top⟩, [])], ⟨[f, q], body⟩⟩
  for tag in [33, 34] do
    let bytes := [UInt8.ofNat tag] ++ seq [3] [2] ++ payload
    let input ← reader bytes 1
    match ← (readStep table |>.run input).run with
    | .error e => throw (IO.userError s!"substitution layout: {repr e}")
    | .ok step =>
      unless step.statement = ⟨[top], [.var p]⟩ do
        throw (IO.userError "substitution conclusion decoded incorrectly")
      let checkFields (i j : Int) (r : SubstRule) :=
        i = -1 && j = 7 && snapshot r = snapshot expected
      let correct := match step.rule with
        | .leftSubst i j r => tag = 33 && checkFields i j r
        | .rightSubst i j r => tag = 34 && checkFields i j r
        | _ => false
      unless correct do throw (IO.userError "substitution fields decoded incorrectly")
    for n in [:bytes.length] do
      let input ← reader (bytes.take n) 1
      match ← (readStep table |>.run input).run with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError s!"accepted truncated substitution {tag}/{n}")
    let rejectPayload (payload : List UInt8) (message : String) := do
      let input ← reader ([UInt8.ofNat tag] ++ seq [] [] ++ payload) 1
      match ← (readStep table |>.run input).run with
      | .error e => unless e.message = message do
          throw (IO.userError s!"wrong substitution decoding error: {repr e}")
      | .ok _ => throw (IO.userError "accepted malformed substitution payload")
    let preamble := be 4 0 ++ be 4 1
    rejectPayload (preamble ++ be 2 65535) "Negative short count"
    rejectPayload (preamble ++ be 2 1 ++ be 4 4294967295) "Negative expression reference"
    rejectPayload (preamble ++ be 2 1 ++ be 4 99) "Invalid expression reference 99"
    let pair := preamble ++ be 2 1 ++ be 4 5 ++ be 4 6
    rejectPayload (pair ++ be 2 65535) "Negative short count"
    rejectPayload (pair ++ be 2 1 ++ be 4 3) "Expected readVariable tree"
    rejectPayload (pair ++ be 2 1 ++ be 4 99) "Invalid expression reference 99"
    rejectPayload (preamble ++ be 2 0 ++ be 2 65535) "Negative short count"
    rejectPayload (preamble ++ be 2 0 ++ be 2 1 ++ be 4 3) "Expected readVariable tree"
    rejectPayload (preamble ++ be 2 0 ++ be 2 0 ++ be 4 99) "Invalid expression reference 99"

-- Retired substitution opcodes fail immediately with a specific diagnostic,
-- even before attempting to read the old payload.
#eval show IO Unit from do
  for tag in [24, 25] do
    let input ← reader [UInt8.ofNat tag] 1
    match ← (readStep #[] |>.run input).run with
    | .error e =>
        unless e.offset = 1 && e.message.startsWith s!"Unsupported legacy substitution tag {tag};" do
          throw (IO.userError s!"wrong retired-opcode diagnostic: {repr e}")
    | .ok _ => throw (IO.userError s!"accepted retired substitution tag {tag}")
