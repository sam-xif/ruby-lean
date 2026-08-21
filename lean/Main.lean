/-
The difftest SUT executable (lean-model-sketch §4): RubyCore-JSON on stdin →
Observation-JSON on stdout.

Exit codes (mirroring the desugar SUT adapter contract):
  0 — observation printed
  3 — out of modeled fragment; reason on stderr
  1 — harness error (bad input, stuck machine); message on stderr
-/
import RubyCore.Obs
import RubyCore.Types.Fragment
import RubyCore.Types.Core
import RubyCore.Types.SigRead
import RubyCore.Types.OpenSelf
import RubyCore.PreludeBoot
import RubyCore.Trace

open RubyCore

def fuelDefault : Nat := 5_000_000
def traceStepsDefault : Nat := 3000

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let fuel := match args with
    | ["--fuel", n] => n.toNat?.getD fuelDefault
    | _ => fuelDefault
  -- `--trace [N]`: emit the step-by-step config trace (playground) instead of
  -- a single Observation. Decode errors still exit 1; a trace always exits 0
  -- (unsupported/stuck are reported inside the JSON `status`).
  let traceSteps : Option Nat := match args with
    | "--trace" :: rest => some (rest.head?.bind (·.toNat?) |>.getD traceStepsDefault)
    | _ => none
  -- Where the trace window starts. A whole-program trace is only viable for a
  -- toy: the Homebrew slice is ~1.1M steps and a snapshot is ~1 KB, so "from
  -- step 0" shows the first 0.4% of a class-definition boot and nothing anyone
  -- wants to look at. `--trace-from N` skips N steps; `--trace-at SUBSTR` skips
  -- to the first step whose *rendered* control contains SUBSTR (`send .compare(`),
  -- which is the form that works when the step index is not knowable in advance.
  let flagArg : String → Option String := fun name =>
    (args.dropWhile (· != name))[1]?
  let traceStart : Option Trace.Start :=
    match flagArg "--trace-at" with
    | some needle => some (.atCtl needle)
    | none => ((flagArg "--trace-from").bind (·.toNat?)).map .atStep
  -- `--steps`: how many steps the program takes, emitting no snapshots — the
  -- number a window is chosen against.
  let countOnly := args.contains "--steps"
  -- `--fragment`: report whether the program is in the **Sorbet fragment** (the
  -- scope any soundness theorem can have — `RubyCore/Types/Fragment.lean`),
  -- with a reason per exclusion. A static query: nothing is executed, so the
  -- prelude is not booted and the answer is independent of model coverage.
  let fragmentOnly := args.contains "--fragment"
  -- `--check`: run the P0 static checker (`RubyCore/Types/Core.lean`) and report
  -- its verdict. Static, like `--fragment`: nothing runs, so the answer is
  -- independent of model coverage and of the prelude. `accept` is the verdict
  -- `Proof/StaticSoundness.check_sound` licenses; `reject` is a claim about our
  -- rules only (`static-soundness-poc.md` §2.2); `unknown` claims nothing.
  let checkOnly := args.contains "--check"
  -- `--sigs`: report the Sorbet signatures the program *declares*, as read off
  -- the AST (`RubyCore/Types/SigRead.lean`). Static, and deliberately separate
  -- from `--check`: reading a declared type is unblocked, whereas concluding
  -- safety about a machine that executes the `T` shim is not (poc doc §8.3).
  let sigsOnly := args.contains "--sigs"
  -- `--assn`: the per-method-body report of `homebrew/assertion-language.md` §11
  -- (rung R1), and the third ratchet §12 R3 asks for. Static, like `--check`.
  --
  -- Two things distinguish it from `--check`. It is **per body** rather than
  -- whole-program, which is the gradient §1's ledger wants — a slice file reads
  -- `unknown` under `--check` until the fragment covers all of it and then flips.
  -- And an `unknown` **carries the atom it wanted**: `needed` is the requirement
  -- `require` could not discharge, where today `unknown` carries no information
  -- at all and the gap has to be reconstructed by `fragment-gap.py`'s
  -- hand-maintained census of `infer`'s match arms — which has been wrong twice.
  --
  -- It changes **no verdict**. `--check` is untouched, and this is a second,
  -- additive query over the same AST.
  let assnOnly := args.contains "--assn"
  match Lean.Json.parse input with
  | .error e =>
    IO.eprintln s!"bad input JSON: {e}"
    return 1
  | .ok j =>
    match Decode.program j with
    | .error e =>
      -- A deliberate decode-time fragment gate (`UNSUPPORTED: …`, e.g. a v4
      -- param kind or additive head the stepper doesn't model yet) is engine
      -- Unsupported (exit 3), not a model bug. Genuine malformations stay 1.
      if "UNSUPPORTED: ".isPrefixOf e then
        IO.eprintln e
        return 3
      else
        IO.eprintln s!"undecodable RubyCore: {e}"
        return 1
    | .ok prog =>
      if sigsOnly then
        let decls := Types.collectSigs prog
        let paramJson := fun (pn : String) (pt : Types.SigTy) =>
          Lean.Json.mkObj [("name", Lean.Json.str pn),
                           ("type", Lean.Json.str pt.render)]
        let declJson := fun (name : String) (d : Types.SigDecl) =>
          Lean.Json.mkObj [
            ("method", Lean.Json.str name),
            ("params", Lean.Json.arr
              (d.params.map (fun p => paramJson p.1 p.2)).toArray),
            -- `null` is `.void`, which is Sorbet saying "no meaningful return"
            -- — not an absence of information.
            ("returns", match d.ret with
              | some t => Lean.Json.str t.render
              | none => Lean.Json.null)]
        IO.println (Lean.Json.mkObj [
          ("sigs", Lean.Json.arr
            (decls.map (fun d => declJson d.1 d.2)).toArray)]).compress
        return 0
      if assnOnly then
        let D := Types.declsOf prog
        let rs := Types.bodyReports D "Object" prog
        let c := Types.census rs
        let one := fun (r : String × String × Types.BodyVerdict) =>
          Lean.Json.mkObj ([
            ("class", Lean.Json.str r.1),
            ("method", Lean.Json.str r.2.1)] ++
            (match r.2.2 with
             | .acceptedUnder ret need rest =>
               [("status", Lean.Json.str "accept"),
                ("type", Lean.Json.str ret.render),
                ("requires", Lean.Json.str need.render),
                ("store", Lean.Json.str rest.render)]
             -- **Parameters open** (L168). `open_params` is printed rather than
             -- inferred from the presence of `params`, because a reader of the
             -- JSON must be able to tell this accept from `acceptedUnder`'s
             -- without knowing that only one of the two can carry parameters:
             -- the two factor through *different* nominal judgements, and only
             -- the latter's is one `check` uses.
             | .acceptedOpenParams ret need rest ps =>
               [("status", Lean.Json.str "accept"),
                ("open_params", Lean.Json.bool true),
                ("params", Lean.Json.arr
                  (ps.map (fun e => Lean.Json.mkObj
                    [("name", Lean.Json.str e.1),
                     ("type", Lean.Json.str e.2.render)])).toArray),
                ("type", Lean.Json.str ret.render),
                ("requires", Lean.Json.str need.render),
                ("store", Lean.Json.str rest.render)]
             | .blocked τ n ps =>
               [("status", Lean.Json.str "unknown"),
                ("needed", Lean.Json.str
                  (τ.render ++ " ~ " ++ n ++ " : (" ++
                    String.intercalate ", " (ps.map Types.ATy.render) ++ ") → _"))]
             | .outOfFragment head =>
               [("status", Lean.Json.str "unknown"),
                ("out_of_fragment", Lean.Json.str head)]))
        IO.println (Lean.Json.mkObj [
          ("bodies", Lean.Json.arr (rs.map one).toArray),
          ("census", Lean.Json.mkObj [
            ("total", Lean.Json.num c.total),
            ("accepted", Lean.Json.num c.accepted),
            ("accepted_params", Lean.Json.num c.acceptedParams),
            ("unconditional", Lean.Json.num c.unconditional),
            ("blocked", Lean.Json.num c.blocked),
            ("out_of_fragment", Lean.Json.num c.outOfFragment)])]).compress
        return 0
      if checkOnly then
        -- **D12: the reported verdict is total** — `decision` is `accept` or
        -- `reject`, never `unknown`, which is `PLAN.md` §1 criterion 2's own
        -- wording and D5's *either verdict is a result*. `reject` claims the
        -- checker did not certify the program, **not** that the program fails.
        --
        -- `verdict` and `basis` are kept beside it rather than replaced, and that
        -- is the whole design: `refuted` (our rules refute) and `uncertified`
        -- (the fragment escaped) are different facts, only the first is what the
        -- `srb` comparison's pinned zero is about, and the tier-4 corpus declares
        -- the three-valued reading. Additive, so no consumer breaks.
        let d := Types.decisionOf prog
        let decision := match d.1 with
          | .accept => "accept"
          | .reject => "reject"
        let basis := match d.2 with
          | .certified => "certified"
          | .refuted => "refuted"
          | .uncertified => "uncertified"
        let verdict := match Types.check prog with
          | .accept => "accept"
          | .reject => "reject"
          | .unknown => "unknown"
        -- The inferred program type accompanies `accept` as a development aid.
        -- It is deliberately *not* a difftest signal: comparing inferred types
        -- against `T.reveal_type` tests neither direction that matters
        -- (`typed-portion-safety.md` §8).
        -- `top := true`, matching `check` (L155). Two calls that can disagree is a
        -- bug waiting to be read as a checker inconsistency: without the flag this
        -- one refuses `class C … end`, so a program `check` accepts came back with
        -- an empty type. Display-only, but the display is what a reader trusts.
        let ty := match Types.infer (Types.declsOf prog) [] prog true with
          | some (t, _, _) => match t with
            | .int => "Integer" | .bool => "Boolean" | .nilT => "NilClass"
            -- `def` evaluates to the method name.
            | .sym => "Symbol"
            -- F1b's class arm. Unreachable today — `infer` has no construct that
            -- produces one — but rendered rather than gated, because the moment a
            -- producer lands this is the line that shows it working.
            | .cls n => n
            -- L183's top type. No expression infers at it — it exists as a
            -- declared *parameter* — so this arm is unreachable and rendered
            -- rather than gated, for the same reason `.cls` was before L151.
            | .any => "T.untyped"
          | none => ""
        IO.println (Lean.Json.mkObj
          ([("decision", Lean.Json.str decision),
            ("basis", Lean.Json.str basis),
            ("verdict", Lean.Json.str verdict)] ++
           (if ty == "" then [] else [("type", Lean.Json.str ty)]))).compress
        return 0
      if fragmentOnly then
        let vs := Types.violationSummary prog
        IO.println (Lean.Json.mkObj [
          ("in_fragment", Lean.Json.bool vs.isEmpty),
          ("violations", Lean.Json.arr (vs.map (fun v => Lean.Json.mkObj [
            ("kind", Lean.Json.str v.kind),
            ("what", Lean.Json.str v.what),
            ("reason", Lean.Json.str v.reason)])).toArray)]).compress
        return 0
      -- Phase 1: boot the prelude (the core library written in RubyCore, L62);
      -- phase 2 runs `prog` on the resulting heap. A prelude failure is a model
      -- bug, never a program outcome → exit 1.
      let m0 ← match Prelude.initWithPrelude prog with
        | .error e =>
          IO.eprintln s!"MODEL PRELUDE FAILURE (bug): {e}"
          return 1
        | .ok m0 => pure m0
      if countOnly then
        IO.println (Trace.countJson m0).compress
        return 0
      if let some maxSteps := traceSteps then
        IO.println (Trace.traceJson maxSteps m0 traceStart).compress
        return 0
      let result := Interp.run fuel m0
      match observe result with
      | .obs obs =>
        IO.println obs.compress
        return 0
      | .unsupported reason =>
        IO.eprintln reason
        return 3
      | .stuck msg =>
        IO.eprintln s!"MODEL STUCK (bug): {msg}"
        return 1
