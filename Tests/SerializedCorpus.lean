import Lisa.CLI

namespace Lisa.Tests.SerializedCorpus

open Imported.Binary

-- Preserve the bytes of a proof exported by the original, non-LCF serializer.
-- Source: lisa-utils/src/test/resources/serialization/tptp-syn040-1.*.b64.
private def treeHex := "010003e288a80000000000053e463e4646010002c2ac0000000000033e464601000170000000000001460300000001000000020300000000000000030100017100000000000146030000000400000005030000000100000005030000000000000007030000000800000002010003e287940000000000053e463e4646010003e288830000000000053e3e5446460000017800000000000154000001500000000000033e5446030000000d0000000c020000000c0000000e030000000b0000000f030000000a00000010010002ceb50000000000053e3e54465403000000120000000f030000000d00000013030000001100000014"
private def proofHex := "0001000e74686542656e63686d61726b2e700000000000050000000100000006000000010000000900000001000000070000000100000002000000010000001500000033000000000100000015fffffffb000000000100000002fffffffc000000000100000007fffffffd000000000100000009fffffffe000000000100000006ffffffff000000000100000015000000000000000001000000020000000100000000010000000700000002000000000100000009000000030000000001000000060000000400000000010000000600000009000000000100000009000000080000000001000000070000000700000000010000000200000006000000000100000015000000050000000001000000020000000d0000000001000000070000000c0000000001000000090000000b0000000001000000060000000a0000000001000000150000000e0000000001000000020000000f000000000100000007000000100000000001000000090000001100000000010000000600000012000000000100000015000000130000000001000000020000001400000000010000000700000015000000000100000009000000160000000001000000060000001700000000010000001500000018000000000100000002000000190000000001000000070000001a0000000001000000090000001b0000000001000000060000001c140001000000020001000000050000002114000100000005000100000002000000201400010000000500000000001f1400000001000000020000001e0000000001000000150000001d00000000010000000200000025000001000000050000000000240000010000000500010000000200000023000001000000020001000000050000002200000100000005000000000028000001000000020001000000050000002a000000000100000002000000270000000001000000020000002d000001000000020001000000050000002c0000010000000500000000002b0300010000000200000000002f000000300000000503000000000000002e0000003100000002"

private def decodeHex (s : String) : ByteArray := Id.run do
  let digits := s.toList.toArray
  let mut bytes := ByteArray.empty
  for i in [:digits.size / 2] do
    let digit (c : Char) := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
    bytes := bytes.push (UInt8.ofNat (digit digits[2 * i]! * 16 + digit digits[2 * i + 1]!))
  return bytes

private def reader (data : ByteArray) (page : Nat) : IO Reader := do
  let position ← IO.mkRef 0
  Reader.create fun requested => do
    let start ← position.get
    let stop := min data.size (start + min requested page)
    position.set stop
    return data.extract start stop

private def checkData {leq : Order} [CheckerOrder leq]
    (page : Nat) (treeData proof : ByteArray) (matching : Imported.Checker.Matching leq := .exact leq) :
    IO (Except DecodeError (Array (NamedProof leq))) := do
  let trees ← reader treeData page
  let .ok table ← (readTrees.run trees).run
    | throw (IO.userError "Original tree fixture failed")
  let stream ← reader proof page
  (readBundle (leq := leq) table false matching |>.run stream).run

private def check (page : Nat) (proof : ByteArray) :=
  checkData (leq := Lisa.Combined.Replay.leq 8) page (decodeHex treeHex) proof
    (Lisa.Combined.Replay.matching 8)

-- Preserve the original failure boundary, then certify the repaired prefix with paged reads.
#eval show IO Unit from do
  let load (path : System.FilePath) := do
    let text ← IO.FS.readFile path
    return decodeHex (text.replace "\n" "" |>.replace "\r" "")
  let trees ← load "Tests/Fixtures/MGT024.trees.hex"
  let proof ← load "Tests/Fixtures/MGT024.proof.hex"
  match ← checkData (leq := Lisa.Combined.leq 8) 7 trees proof with
  | .error e =>
      unless e.offset = 824 && e.message.startsWith "Invalid step 39 (weakening):" do
        throw (IO.userError s!"Original Weakening boundary changed: {repr e}")
  | .ok _ => throw (IO.userError "Contextual baseline unexpectedly accepted quantified Weakening")
  for (page, optimized) in [(1, false), (7, false), (65536, false), (1, true), (7, true), (65536, true)] do
    let matching := if optimized then Lisa.Combined.Replay.matching 8 else .exact (Lisa.Combined.Replay.leq 8)
    match ← checkData (leq := Lisa.Combined.Replay.leq 8) page trees proof matching with
    | .error e => throw (IO.userError s!"Quantified Weakening fixture failed: {repr e}")
    | .ok results =>
        let some (result : NamedProof (Lisa.Combined.Replay.leq 8)) := results[0]?
          | throw (IO.userError "Missing quantified theorem")
        unless results.size = 1 && result.name = "theBenchmark.p" &&
            result.steps = 40 && result.imports = 7 do
          throw (IO.userError "Quantified fixture metadata changed")
        if h : result.checked.assumptions = ∅ then
          let closed : Imported.Checker.ClosedChecked (Lisa.Combined.Replay.leq 8)
              (result.checked.statement) := ⟨by simpa [h] using result.checked.certificate⟩
          have _ := Lisa.Combined.certificate_sound closed
          pure ()
        else throw (IO.userError "Quantified fixture gained unresolved assumptions")

#eval show IO Unit from do
  for page in [1, 2, 7, 65536] do
    match ← check page (decodeHex proofHex) with
    | .error e => throw (IO.userError s!"Original serialized proof failed: {repr e}")
    | .ok results =>
      let some result := results[0]? | throw (IO.userError "Missing original theorem")
      unless results.size = 1 && result.name = "theBenchmark.p" &&
          result.steps = 51 && result.imports = 5 &&
          result.checked.assumptions.card = 3 do
        throw (IO.userError "Original proof metadata or assumption tracking changed")
      unless result.checked.statement =
          ⟨[], []⟩ do
        throw (IO.userError "Original proof conclusion decoded incorrectly")
  let proof := decodeHex proofHex
  for length in [0, 1, 2, 10, proof.size - 1] do
    match ← check 7 (proof.extract 0 length) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"Accepted truncated original proof: {length}")
  match ← check 7 (proof.push 0) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Accepted trailing bytes in original proof")

#guard (Lisa.CLI.parse ["--budget", "0", "--limit", "2", "--closed", "--trace", "proof"] {}).isOk
#guard !(Lisa.CLI.parse [] {}).isOk
#guard !(Lisa.CLI.parse ["--limit", "0", "proof"] {}).isOk
#guard !(Lisa.CLI.parse ["--limit", "-1", "proof"] {}).isOk
#guard !(Lisa.CLI.parse ["--budget", "invalid", "proof"] {}).isOk
#guard !(Lisa.CLI.parse ["--trace", "--unknown", "proof"] {}).isOk
#guard !(Lisa.CLI.parse ["--budget"] {}).isOk

#eval IO.FS.withTempDir fun directory => do
  let base := directory / "proof.with.dots"
  let trees : System.FilePath := base.toString ++ ".trees"
  let proof : System.FilePath := base.toString ++ ".proof"
  IO.FS.writeBinFile trees (decodeHex treeHex)
  IO.FS.writeBinFile proof (decodeHex proofHex)
  IO.FS.writeFile (directory / "unrelated.txt") "Ignore this file"
  let inputs ← Lisa.CLI.prefixes #[directory, directory, trees, proof, base]
  unless inputs = #[base] do
    throw (IO.userError s!"Duplicate inputs or lost dotted prefix: {repr inputs}")
  match ← Lisa.Combined.checkFiles 8 trees proof with
  | .error e => throw (IO.userError s!"Paged file checking failed: {repr e}")
  | .ok results =>
    unless results.size = 1 do throw (IO.userError "Wrong file result count")
  let empty := directory / "empty"
  IO.FS.createDir empty
  unless (← Lisa.CLI.prefixes #[empty]).isEmpty do
    throw (IO.userError "Empty directory produced a bundle")

end Lisa.Tests.SerializedCorpus
