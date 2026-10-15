import Lisa.CombinedCached
import Std.Data.HashSet.Basic

namespace Lisa.CLI

open Imported.Binary

structure Options where
  budget : Nat := 8
  limit : Option Nat := none
  closed : Bool := false
  trace : Bool := false
  olCache : Option Orthologic.Nnf.MemoConfig := none
  paths : Array System.FilePath := #[]
deriving Repr

/-- Parse checker options and preserve the input paths. -/
def parse : List String → Options → Except String Options
  | [], options =>
    if options.paths.isEmpty then .error "Provide a proof prefix or directory"
    else .ok options
  | "--budget" :: n :: rest, options => do
    let some budget := n.toNat? | throw "Expected a natural-number budget"
    parse rest { options with budget }
  | "--limit" :: n :: rest, options => do
    let some limit := n.toNat? | throw "Expected a positive bundle limit"
    if limit = 0 then throw "Expected a positive bundle limit"
    parse rest { options with limit := some limit }
  | "--closed" :: rest, options => parse rest { options with closed := true }
  | "--trace" :: rest, options => parse rest { options with trace := true }
  | "--ol-cache" :: mode :: rest, options => do
    let config ← match mode with
      | "normalization" => pure { comparison := false }
      | "comparison" => pure { normalization := false }
      | "both" => pure {}
      | _ => .error "Expected OL cache mode: normalization, comparison, or both"
    parse rest { options with olCache := some config }
  | arg :: rest, options =>
    if arg.startsWith "--" then .error s!"Unknown or incomplete option: {arg}"
    else parse rest { options with paths := options.paths.push arg }

/-- Find paired-stream prefixes, deduplicating directories and both file extensions. -/
def prefixes (paths : Array System.FilePath) : IO (Array System.FilePath) := do
  let mut pending := paths.map fun p => (p, true)
  let mut directories : Std.HashSet String := ∅
  let mut found : Std.HashSet String := ∅
  while !pending.isEmpty do
    let some (path, explicit) := pending.back? | break
    pending := pending.pop
    if ← path.isDir then
      let canonical ← IO.FS.realPath path
      unless directories.contains canonical.toString do
        directories := directories.insert canonical.toString
        for entry in ← path.readDir do
          pending := pending.push (entry.path, false)
    else if path.extension = some "trees" || path.extension = some "proof" then
      found := found.insert (path.withExtension "").toString
    else if explicit then
      found := found.insert path.toString
  return found.toArray.map System.FilePath.mk |>.qsort (fun a b => a.toString < b.toString)

private def cell (s : String) : String :=
  s.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " "

private def pair (base : System.FilePath) : System.FilePath × System.FilePath :=
  (base.toString ++ ".trees", base.toString ++ ".proof")

/-- Check selected bundles, reporting validity relative to their recorded assumptions. -/
def run (options : Options) : IO UInt32 := do
  let inputs ← prefixes options.paths
  let inputs := match options.limit with
    | none => inputs
    | some n => inputs.extract 0 (min n inputs.size)
  if inputs.isEmpty then
    IO.eprintln "No .trees/.proof pairs found"
    return 1
  let stdout ← IO.getStdout
  stdout.putStrLn "file\tname\tstatus\tsteps\timports\tassumptions\telapsed_ms\tdetail"
  let mut passed := 0
  let mut failed := 0
  for base in inputs do
    let start ← IO.monoMsNow
    try
      let (trees, proof) := pair base
      unless (← trees.pathExists) && (← proof.pathExists) do
        throw (IO.userError "Missing .trees/.proof partner")
      let checked ← match options.olCache with
        | none => Combined.checkFiles options.budget trees proof options.trace
        | some config => Combined.Cached.checkFiles config options.budget trees proof options.trace
      match checked with
      | .error e =>
        failed := failed + 1
        stdout.putStrLn s!"{cell base.toString}\t\tFAIL\t\t\t\t{(← IO.monoMsNow) - start}\tbyte {e.offset}: {cell e.message}"
      | .ok results =>
        let elapsed := (← IO.monoMsNow) - start
        if results.isEmpty then
          failed := failed + 1
          stdout.putStrLn s!"{cell base.toString}\t\tFAIL\t0\t0\t0\t{elapsed}\tNo named proofs"
        for result in results do
          let reject := options.closed && result.checked.assumptions != ∅
          if reject then failed := failed + 1 else passed := passed + 1
          let status := if reject then "FAIL" else "PASS"
          let detail := if reject then "Unresolved assumptions" else "Relative to recorded assumptions"
          stdout.putStrLn s!"{cell base.toString}\t{cell result.name}\t{status}\t{result.steps}\t{result.imports}\t{result.checked.assumptions.card}\t{elapsed}\t{detail}"
    catch e =>
      failed := failed + 1
      stdout.putStrLn s!"{cell base.toString}\t\tFAIL\t\t\t\t{(← IO.monoMsNow) - start}\t{cell e.toString}"
    stdout.flush
  IO.eprintln s!"{passed} named proofs passed; {failed} failures; {inputs.size} bundles visited."
  return (if failed = 0 then 0 else 1 : UInt32)

/-- Run the paged linear proof checker with a configurable contextual budget. -/
def main (args : List String) : IO UInt32 := do
  if args = ["--help"] then
    IO.println "Usage: lisa-checker [--budget N] [--limit N] [--closed] [--trace] [--ol-cache normalization|comparison|both] PREFIX|DIRECTORY ..."
    return 0
  match parse args {} with
  | .error message => IO.eprintln message; return 2
  | .ok options => run options

end Lisa.CLI
