import Ratchet.Corpus
import Ratchet.Rungs13

/-!
The ratchet runner: load every `corpus/*.json` entry (real desugared Ruby + a
certificate) and check `validate`'s actual verdict against the recorded expectation.
See `AGENTS.md` for how to read the report and `scripts/run_ratchet.sh` for the
one-line invocation.

Two numbers, not one, since `chk` gained a claim-fallback (`Ratchet/Validate.lean`): a
rung can validate **structurally** (the checker synthesized the type itself) or
**claim-assisted** (a certificate claim on some node supplied it, and a claim is
*trusted* — `Judge.claim` in `Ratchet/Judge.lean` has no justification behind it). Both
are legitimate ways for a rung to be climbed — the claims escape hatch is the intended
route for e.g. `unknown-method-with-claim` — but they carry very different weight, so
the report separates them rather than summing them into one flattering total.
"Structural" is computed by re-running `validate` with the certificate emptied.
-/

open Ratchet
open Lean (Json)

structure EntryReport where
  id : String
  tier : Nat
  validateActual : Bool
  validateOk : Bool
  /-- Did it validate with **no** certificate at all? Then no trusted claim was used. -/
  structural : Bool
  falseReason : Option String

def runEntry (e : CorpusEntry) : EntryReport :=
  let validateActual := validate e.cert e.program
  { id := e.id, tier := e.tier
    validateActual := validateActual
    validateOk := validateActual == e.expectValidate
    structural := validate ⟨[]⟩ e.program
    falseReason := e.falseReason }

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
    let tag := match r.falseReason with
      | some reason => s!" [{reason}]"
      | none => ""
    let how :=
      if !r.validateActual then ""
      else if r.structural then " structural"
      else " claim-assisted"
    IO.println s!"tier {r.tier} {r.id}{tag}: validate={r.validateActual}{how} ({mark})"

  IO.println "\n--- tier summary (certified well-typed / total) ---"
  let tiers := (reports.map (·.tier)).eraseDups |>.toArray |>.qsort (· < ·) |>.toList
  for t in tiers do
    let tReports := reports.filter (·.tier == t)
    let certified := tReports.filter (·.validateActual)
    let structural := tReports.filter (·.structural)
    IO.println s!"tier {t}: {certified.length}/{tReports.length} certified well-typed \
({structural.length} structural, {certified.length - structural.length} claim-assisted)"

  -- Always shown, independent of pass/fail: the standing list of rungs whose target is
  -- permanently `false` because the *cert language* (not just `chk`'s implementation)
  -- cannot state a sufficient claim. This is the thing worth watching for growth —
  -- each entry names a concrete `Ty` extension, not a rule to implement.
  let gaps := reports.filter (fun r => r.falseReason == some "cert_language_gap")
  IO.println s!"\n--- flagged: cert language gaps ({gaps.length}) ---"
  for g in gaps do
    IO.println s!"  {g.id} (tier {g.tier})"

  IO.println s!"\nhand-authored derivations on file (Ratchet/Rungs13.lean): {rungs13.length} \
-- each one a `Judge` proof term, cross-checked against the real semantics by `lake exe check13`"

  let mismatches := reports.filter (fun r => !r.validateOk)
  IO.println s!"\nrungs where validate's current answer differs from the recorded target (expect_validate): {mismatches.length}"
  IO.println "(chk covers tier 1 + Integer/String arithmetic today, plus the claim-fallback; \
everything above that is the climb still ahead -- not a bug; see AGENTS.md)"
  for m in mismatches do
    IO.eprintln s!"  not yet climbed: {m.id} (tier {m.tier})"

  if mismatches.isEmpty then
    IO.println "RATCHET OK"
    return 0
  else
    IO.println "RATCHET: climb remaining"
    return 1
