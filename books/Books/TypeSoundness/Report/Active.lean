import Books.TypeSoundness.Registry.SoundnessAudit
import Checker.Check.Rung

/-!
# The corpus report

What `scripts/check-soundness.sh` prints last: how many of the checker's typing
rules are registered with a soundness proof, and which corpus programs the real
`validateD` accepts. A program that is not accepted is listed with the reason,
which is read from the checker's own trace of the derivation it was given.

The run fails if

* a program the corpus marks as one the checker must reject is accepted,
* Sorbet's verdict on a program differs from the one recorded for it,
* a stage before the checker fails on a program it did not fail on before, or
* the set of accepted programs differs from `corpus/accepted.txt`.

The last is what stops an accepted program from silently becoming a declined
one. When a change makes the checker accept more, record it with
`scripts/check-soundness.sh --record`.
-/
namespace Checker.Soundness.Typed.ActiveReport
open Checker

structure Row where
  rung : Rung
  accepted : Bool
  gated : List String
  reason : String

def classify (r : Rung) : Row :=
  let accepted := r.verdict
  let gated := match r.program, r.deriv with
    | some p, some d => match Audit.check fuelD [] p d with
      | some c => (c.rulesUsed.filter (!clinkEnabled ·)).eraseDups
      | none => []
    | _, _ => []
  let reason := if accepted then "accepted" else if !gated.isEmpty then
      "uses rules with no registered proof: " ++ String.intercalate ", " gated
    else match r.stage with
      | .failed st why => s!"upstream {st}: {why}"
      | .blocked why => s!"emitter: {why}"
      | .ok => if !r.expectValidate then r.falseReason.getD "must be rejected, and is"
        else "the checker declined the emitted derivation"
  { rung := r, accepted, gated, reason }

def loadRung (path : System.FilePath) : IO Rung := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= Rung.ofJson? with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The value following `flag` in `args`, if any. -/
def flagValue (args : List String) (flag : String) : Option String :=
  (args.dropWhile (· != flag))[1]?

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "build"
  let quiet := args.contains "--quiet"
  let entries ← dir.readDir
  let paths := entries.map (·.path) |>.filter (·.toString.endsWith ".rung.json")
    |>.qsort (fun a b => a.toString < b.toString)
  if paths.isEmpty then
    IO.eprintln s!"no built corpus programs under {dir}"
    return 1
  let rungs ← paths.toList.mapM loadRung
  let rows := rungs.map classify
  let accepted := rows.filter (·.accepted)
  let pending := rows.filter (fun row => !row.accepted && row.rung.expectValidate)
  let negatives := rows.filter (fun row => !row.rung.expectValidate)
  let unexpectedAccepts := negatives.filter (·.accepted)
  let sorbetMoved := rows.filter (fun row => row.rung.srbClean != row.rung.expectSorbet)
  let newFailures := rows.filter fun row => match row.rung.stage with
    | .failed _ _ => row.rung.knownUpstreamFailure.isNone
    | _ => false
  IO.println s!"typing rules with a soundness proof: {dRegisteredRules.length}/{dAllRules.length}"
  if !dGatedRules.isEmpty then
    IO.println s!"  without one (the checker refuses any derivation that uses them): \
{String.intercalate ", " dGatedRules}"
  if !quiet then
    IO.println s!"  {String.intercalate ", " dRegisteredRules}"
  IO.println s!"corpus programs accepted by validateD: {accepted.length}/{rows.length}"
  IO.println s!"  must be rejected, and are: \
{negatives.length - unexpectedAccepts.length}/{negatives.length}"
  IO.println s!"  not accepted yet: {pending.length}"
  if !quiet then
    for row in rows do
      IO.println s!"  {row.rung.base}: {row.reason}"
  else
    for row in pending.take 20 do
      IO.println s!"    {row.rung.base}: {row.reason}"
    if pending.length > 20 then
      IO.println s!"    ... and {pending.length - 20} more (--verbose lists them all)"
  for row in unexpectedAccepts do
    IO.eprintln s!"FAIL: accepted a program that must be rejected: {row.rung.base}"
  for row in sorbetMoved do
    IO.eprintln s!"FAIL: Sorbet's verdict changed: {row.rung.base}"
  for row in newFailures do
    IO.eprintln s!"FAIL: {row.rung.base}: {row.reason}"
  let mut failed := !unexpectedAccepts.isEmpty || !sorbetMoved.isEmpty || !newFailures.isEmpty
  let names := accepted.map (·.rung.base)
  if let some file := flagValue args "--record" then
    IO.FS.writeFile file (String.join (names.map (· ++ "\n")))
    IO.println s!"recorded {names.length} accepted programs in {file}"
  else if let some file := flagValue args "--accepted" then
    let recorded := (← IO.FS.lines file).toList.filter (· != "")
    -- Only programs in this run are compared, so `--only` still works.
    let inRun := rows.map (·.rung.base)
    for name in recorded do
      if inRun.contains name && !names.contains name then
        IO.eprintln s!"FAIL: no longer accepted: {name}"
        failed := true
    for name in names do
      if !recorded.contains name then
        IO.eprintln s!"FAIL: newly accepted, but not in {file}: {name} \
(record it: scripts/check-soundness.sh --record)"
        failed := true
  return if failed then 1 else 0
end Checker.Soundness.Typed.ActiveReport
