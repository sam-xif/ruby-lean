/-
The observation function (artifact 00 §2 / difftest observation.py):
obs = (stdout, result_repr = inspect(final value), exception = (class, msg)),
heap projection deferred exactly as the engine's v1 does.
-/
import RubyCore.Interp
import Json

namespace RubyCore

-- `Json` is this project's vendored copy of Lean's (`Json.lean`), at the root
-- namespace, so there is nothing to open.

inductive ObsResult where
  /-- A comparable observation (JSON matching Observation.to_json). -/
  | obs (j : Json)
  /-- Out of the modeled fragment, with a reason (SUT exit 3). -/
  | unsupported (reason : String)
  /-- The model itself is broken (stuck state) — a harness error, never
      silently mapped to Unsupported-by-design. Still exits 3 but the
      reason is prefixed so triage can spot it. -/
  | stuck (msg : String)

def obsJson (stdout : String) (result : Option String)
    (exc : Option (String × String)) : Json :=
  Json.mkObj [
    ("stdout", Json.str stdout),
    ("result_repr", match result with
      | some r => Json.str r
      | none => Json.null),
    ("exception", match exc with
      | some (c, msg) => Json.arr #[Json.str c, Json.str msg]
      | none => Json.null),
    ("timed_out", Json.bool false)
  ]

def observe (r : Interp.RunResult) : ObsResult :=
  match r with
  | .value v m =>
    match Builtins.inspectP m v with
    | .ok repr => .obs (obsJson m.out (some repr) none)
    | .error e => .unsupported s!"final-value inspect: {e}"
  | .uncaught exc m =>
    let cls := className m.heap (realClassOf m.heap exc)
    let msg := match exc with
      | .ref o => match (m.heap.get o).payload with
        | .exc s => s
        | _ => ""
      | _ => ""
    -- The control observes `__exc.message`, which **dispatches** — and
    -- `Exception#message` is `to_s`, so a user `to_s` or `message` decides what the
    -- observation says. Reading the payload answered the raw message instead, and
    -- there is no machine left to dispatch in: the program has ended, exactly as in
    -- `result_repr` below (L131). So refuse rather than answer the payload.
    if Builtins.programOverridden m.heap ["to_s", "message"] (classOf m.heap exc) then
      .unsupported
        "uncaught exception whose message is dispatched (a user to_s/message), computed after the program has ended"
    else
    .obs (obsJson m.out none (some (cls, msg)))
  | .unsupported reason _ => .unsupported reason
  | .outOfFuel _ => .unsupported "out of fuel"
  | .stuck msg _ => .stuck msg

end RubyCore
