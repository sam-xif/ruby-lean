import Denote.Clink.SoundnessAudit
import Ratchet.Check.Rung

/-! Progress under the committed active registry. Only production validateD
acceptance counts as a climbed corpus rung. Rejection reasons come from the
proof-indexed trace, including companion/body rules, rather than AST guesses.
Historical full-profile targets and floors belong to the optional full audit. -/
namespace Ratchet.Denote.Typed.ActiveReport
open Ratchet

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
  let reason := if accepted then "climbed" else if !gated.isEmpty then
      "gated: " ++ String.intercalate ", " gated
    else match r.stage with
      | .failed st why => s!"upstream {st}: {why}"
      | .blocked why => s!"emitter: {why}"
      | .ok => if !r.expectValidate then r.falseReason.getD "negative control"
        else "checker declined the emitted certificate"
  { rung := r, accepted, gated, reason }

def loadRung (path : System.FilePath) : IO Rung := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= Rung.ofJson? with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"{path}: {e}")

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "build"
  let quiet := args.contains "--quiet"
  let entries ← dir.readDir
  let paths := entries.map (·.path) |>.filter (·.toString.endsWith ".rung.json")
    |>.qsort (fun a b => a.toString < b.toString)
  if paths.isEmpty then
    IO.eprintln s!"no built rungs under {dir}"
    return 1
  let rungs ← paths.toList.mapM loadRung
  let rows := rungs.map classify
  let climbed := rows.filter (·.accepted)
  let pending := rows.filter (fun row => !row.accepted && row.rung.expectValidate)
  let negatives := rows.filter (fun row => !row.rung.expectValidate)
  let unexpectedAccepts := negatives.filter (·.accepted)
  let sorbetMoved := rows.filter (fun row => row.rung.srbClean != row.rung.expectSorbet)
  let newFailures := rows.filter fun row => match row.rung.stage with
    | .failed _ _ => row.rung.knownUpstreamFailure.isNone
    | _ => false
  IO.println s!"ACTIVE CLINKS: {dRegisteredRules.length}/{dAllRules.length} climbed; {dGatedRules.length} gated"
  IO.println s!"  enabled: {String.intercalate ", " dRegisteredRules}"
  IO.println s!"CORPUS RUNGS: {climbed.length}/{rows.length} climbed by validateD; {pending.length} positive goals remaining"
  IO.println s!"  accepted prefix: {(rows.takeWhile (·.accepted)).length}; negative controls: {negatives.length - unexpectedAccepts.length}/{negatives.length} rejected"
  if !quiet then
    for row in rows do
      IO.println s!"  {row.rung.base}: {row.reason}"
  else
    for row in pending.take 20 do
      IO.println s!"  {row.rung.base}: {row.reason}"
    if pending.length > 20 then IO.println s!"  ... and {pending.length - 20} more positive goals"
  for row in unexpectedAccepts do
    IO.eprintln s!"negative control accepted: {row.rung.base}"
  for row in sorbetMoved do
    IO.eprintln s!"Sorbet verdict moved: {row.rung.base}"
  for row in newFailures do
    IO.eprintln s!"new upstream failure: {row.rung.base}: {row.reason}"
  if !unexpectedAccepts.isEmpty || !sorbetMoved.isEmpty || !newFailures.isEmpty then return 1
  return 0
end Ratchet.Denote.Typed.ActiveReport
