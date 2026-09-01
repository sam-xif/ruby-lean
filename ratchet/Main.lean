import Ratchet.Corpus

/-!
The ratchet runner: load every `corpus/*.json` entry (real desugared Ruby + a
certificate) and check `validate`'s actual verdict against the recorded expectation.
See `AGENTS.md` for how to read the report and `scripts/run_ratchet.sh` for the
one-line invocation.
-/

open Ratchet
open Lean (Json)

structure EntryReport where
  id : String
  tier : Nat
  validateActual : Bool
  validateOk : Bool

def runEntry (e : CorpusEntry) : EntryReport :=
  let validateActual := validate e.cert e.program
  { id := e.id, tier := e.tier
    validateActual := validateActual
    validateOk := validateActual == e.expectValidate }

def loadEntry (p : System.FilePath) : IO CorpusEntry := do
  let contents ← IO.FS.readFile p
  match Json.parse contents with
  | .error e => throw (IO.userError s!"{p}: JSON parse error: {e}")
  | .ok j =>
    match CorpusEntry.ofJson? j with
    | .error e => throw (IO.userError s!"{p}: {e}")
    | .ok entry => pure entry

def main (args : List String) : IO UInt32 := do
  let corpusDir : System.FilePath := args.headD "corpus"
  let dirEntries ← corpusDir.readDir
  let files := (dirEntries.map (·.path)).toList.filter (fun p => p.toString.endsWith ".json")
  let sorted := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let entries ← sorted.mapM loadEntry
  if entries.isEmpty then
    IO.eprintln s!"no corpus entries found under {corpusDir}"
    return 1
  let reports := entries.map runEntry

  for r in reports do
    let mark := if r.validateOk then "ok" else "MISMATCH"
    IO.println s!"tier {r.tier} {r.id}: validate={r.validateActual} ({mark})"

  IO.println "\n--- tier summary (certified well-typed / total) ---"
  let tiers := (reports.map (·.tier)).eraseDups |>.toArray |>.qsort (· < ·) |>.toList
  for t in tiers do
    let tReports := reports.filter (·.tier == t)
    let certified := tReports.filter (·.validateActual)
    IO.println s!"tier {t}: {certified.length}/{tReports.length} certified well-typed"

  let mismatches := reports.filter (fun r => !r.validateOk)
  IO.println s!"\nexpectation mismatches (bugs in this harness, not in the ladder design): {mismatches.length}"
  for m in mismatches do
    IO.eprintln s!"  MISMATCH: {m.id} (tier {m.tier})"

  if mismatches.isEmpty then
    IO.println "RATCHET OK"
    return 0
  else
    IO.println "RATCHET FAILED"
    return 1
