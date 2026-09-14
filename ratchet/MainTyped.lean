import Ratchet.Rung

/-!
`lake exe ratchetd` -- the typed ratchet's report.

The **fifth** stage of the pipeline `scripts/build_corpus.py` runs, and the only trusted
one: everything it reads is the output of four untrusted stages (Sorbet, the strip stack,
the desugarer, the emitter), and the only thing it believes is the *program*. The
derivation is checked, never trusted.

    scripts/build_corpus.py      # stages 1-4, into build/
    lake exe ratchetd build      # stage 5

**`validateD` types.** `Ratchet/Check.lean`'s `check` matches the program, derives the type
itself, compares every `Ty` the certificate claims, and **returns the `DJudge` derivation** —
so a `true` below is "there is a derivation of this program in the certified judgment", with
no theorem in between (the checker's *type* is the syntactic soundness statement).
All twelve expression rules and four list companions now have answer-typed semantic proofs.
`lake exe semladder build` checks concrete safety proofs against the stripped corpus and
prints the remaining unmet goals.


The headline number is **ladder reach**: the length of the leading run of rungs that meet
their recorded target. A prefix, not a total, because that is what "we are at rung N" means
and because a rung that certifies out of order tells you nothing about the ones before it.
-/

open Ratchet
open Lean (Json)

structure Row where
  rung : Rung
  verdict : Bool

/-- **The ratchet.** The recorded ladder reach; a rung once climbed never un-climbs
(`AGENTS.md`). Raise it when the reach grows; a drop is a regression and the exit code says
so. Unlike the old syntactic ladder's number this one is a prefix, so it cannot be inflated
by a rung that happens to certify out of order. -/
def ladderFloor : Nat := 51

def loadRung (p : System.FilePath) : IO Rung := do
  let contents ← IO.FS.readFile p
  match Json.parse contents with
  | .error e => throw (IO.userError s!"{p}: JSON parse error: {e}")
  | .ok j =>
    match Rung.ofJson? j with
    | .error e => throw (IO.userError s!"{p}: {e}")
    | .ok r => pure r

def stageLabel : RungStage → String
  | .ok => "ok"
  | .blocked why => s!"blocked: {why}"
  | .failed st why => s!"FAILED at {st}: {why}"

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "build"
  let dirEntries ← dir.readDir
  let files := (dirEntries.map (·.path)).toList.filter (·.toString.endsWith ".rung.json")
  let sorted := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  if sorted.isEmpty then
    IO.eprintln s!"no built rungs under {dir} -- run scripts/build_corpus.py first"
    return 1
  let rungs ← sorted.mapM loadRung
  let rows := rungs.map (fun r => { rung := r, verdict := r.verdict : Row })

  IO.println "=== per rung (sorbet | emitter | validateD) ==="
  for row in rows do
    let r := row.rung
    let srb := if r.srbClean then "srb-ok" else "srb-ERRORS"
    IO.println s!"tier {r.tier} {r.id}: {srb} | sigs={r.sigs} | \
{stageLabel r.stage} | validateD={row.verdict}"

  let n := rows.length
  let clean := (rows.filter (·.rung.srbClean)).length
  let sorbetAsExpected := (rows.filter (fun x => x.rung.srbClean == x.rung.expectSorbet)).length
  let emitted := (rows.filter (fun x => match x.rung.stage with | .ok => true | _ => false)).length
  let blocked := (rows.filter (fun x => match x.rung.stage with | .blocked _ => true | _ => false)).length
  let failedRows := rows.filter (fun x => match x.rung.stage with | .failed _ _ => true | _ => false)
  let failed := failedRows.length
  let newFailures := failedRows.filter (·.rung.knownUpstreamFailure.isNone)
  let sorbetDisagree := rows.filter (fun x => x.rung.srbClean != x.rung.expectSorbet)
  let certified := (rows.filter (·.verdict)).length
  -- The ladder: rungs that meet their recorded target, and the leading run of them.
  let met := rows.map (fun x => x.verdict == x.rung.expectValidate)
  let reach := (met.takeWhile id).length
  let frontier := rows.drop reach |>.head?
  let withSigs := (rows.filter (·.rung.sigs > 0)).length
  let dropping := (rows.filter (!·.rung.dropped.isEmpty)).length

  IO.println "\n--- the pipeline, stage by stage ---"
  IO.println s!"rungs:                              {n}"
  IO.println s!"  srb typechecks the annotation:    {clean}/{n} \
({sorbetAsExpected}/{n} agree with expect_sorbet)"
  IO.println s!"  rungs declaring a usable sig:     {withSigs}/{n} \
({dropping} rungs have at least one signature srb resolved but `Ty` cannot express)"
  IO.println s!"  emitter produced a derivation:    {emitted}/{n} \
(blocked {blocked}, upstream failure {failed} -- all recorded)"
  IO.println s!"  validateD (typing) accepted it:   {certified}/{n}"
  IO.println s!"  rungs meeting their target:       {(met.filter id).length}/{n}"
  IO.println s!"\nLADDER REACH: {reach} rungs \
(the leading run whose verdict equals its recorded expect_validate)"
  match frontier with
  | some f =>
    IO.println s!"  frontier: {f.rung.base} (tier {f.rung.tier}) -- \
expect_validate={f.rung.expectValidate}, got {f.verdict}; {stageLabel f.rung.stage}"
  | none => IO.println "  frontier: none -- every rung meets its target"

  IO.println "\n--- what the emitter blocked on (the fragment boundary, counted) ---"
  let reasons := rows.filterMap (fun x => match x.rung.stage with
    | .blocked why => some why | _ => none)
  let uniq := reasons.eraseDups
  let counted := uniq.map (fun w => (w, (reasons.filter (· == w)).length))
  let ranked := counted.toArray.qsort (fun a b => a.2 > b.2) |>.toList
  for (why, k) in ranked do
    IO.println s!"  {k}x  {why}"

  IO.println "\n--- tier summary (derivation emitted and shape-checked / total) ---"
  let tiers := (rows.map (·.rung.tier)).eraseDups.toArray.qsort (· < ·) |>.toList
  for t in tiers do
    let ts := rows.filter (·.rung.tier == t)
    IO.println s!"tier {t}: {(ts.filter (·.verdict)).length}/{ts.length}"

  IO.println "\nNOTE: a `true` above means a `DJudge` derivation exists. Every judgment rule \
has an answer-typed semantic proof. `lake exe semladder build` checks each accepted rung's \
end-to-end safety proof against the actual stripped program."


  -- Two things are failures rather than measurements, and both are ratchets
  -- (`scripts/record_baseline.py`): an upstream stage that errored and was not already
  -- recorded as doing so, and a rung whose Sorbet verdict moved. A *block* is neither:
  -- it is the fragment reporting its own boundary.
  for x in sorbetDisagree do
    IO.eprintln s!"  sorbet verdict moved: {x.rung.id} \
(expect_sorbet={x.rung.expectSorbet}, srb says {x.rung.srbClean})"
  for x in newFailures do
    IO.eprintln s!"  NEW upstream failure: {x.rung.id}: {stageLabel x.rung.stage}"
  if reach < ladderFloor then
    IO.eprintln s!"  LADDER REGRESSED: reach {reach}, floor {ladderFloor}"
  if !newFailures.isEmpty || !sorbetDisagree.isEmpty || reach < ladderFloor then
    IO.println s!"RATCHETD: {newFailures.length} new upstream failure(s), \
{sorbetDisagree.length} moved Sorbet verdict(s), reach {reach}/{ladderFloor}"
    return 1
  IO.println "RATCHETD OK (pipeline green; see the note above for what that does not mean)"
  return 0
