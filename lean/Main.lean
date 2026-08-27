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
import RubyCore.Types.Program
import RubyCore.Cert.Json
import RubyCore.Judgment.Json
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
  -- `--assn-program`: L263/L264's **whole-program** open verdict, and it is a third
  -- query rather than a mode of `--assn` for a stated reason — `--assn`'s per-body
  -- census is a *consumed* number (`homebrew/fragment-gap.py`'s third ratchet), so it
  -- must stay byte-identical.
  --
  -- What distinguishes it from both existing static queries. Against `--check`: it
  -- accepts programs with `def`s and `class`es whose *declarations do not exist yet*,
  -- and answers what the types would have to be rather than whether they are known.
  -- Against `--assn`: the bodies share **one store**, so a class's own `def`s cancel
  -- against its own bodies' requirements (`Types/Discharge.lean`) — which is the thing
  -- a per-body pass structurally cannot do, since it hands every body a fresh store.
  --
  -- **An `accept` here is the weakest of the three**, and the JSON says so in the
  -- `means` field rather than leaving it to be inferred: *types under these class
  -- obligations*. `check`'s `accept` is the only one `check_sound` licenses.
  let assnProgOnly := args.contains "--assn-program"
  -- `--certify FILE`: **replay a certificate** (`docs/semantics/certificate-language.md`).
  -- The program comes in on stdin as always; `FILE` holds the certificate JSON the
  -- (untrusted) `certify/` emitters produce. `validate` re-checks it and
  -- `Proof/Cert/Sound.lean`'s `validate_sound` is what an accept means.
  --
  -- A fourth static query rather than a mode of the other three, for `--assn-program`'s
  -- reason: `--check`'s and `--assn`'s numbers are consumed ratchets and must stay
  -- byte-identical. This one reads a *second input*, which is the whole difference — it
  -- is the only query whose answer depends on something other than the program.
  let certifyFile : Option String := flagArg "--certify"
  -- `--certify-j FILE`: **replay a judgment-layer certificate** (`docs/semantics/
  -- judgment-layer.md` §4(3), J25). `FILE` holds a `JCert` JSON — claimed rows plus
  -- a `Deriv` tree — and the trusted `validateJ` re-checks it against the program on
  -- stdin. An accept means `Proof/Judgment/Adequacy.lean`'s `validateJ_certifies`
  -- applies: no reachable outcome is type-stuck, conditional on exactly the printed
  -- `carries` rows' residue (`EntryOkJ` each), and unconditional when there are none.
  -- Same second-input rationale as `--certify`; same reject-not-crash discipline.
  let certifyJFile : Option String := flagArg "--certify-j"
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
        -- **`preludeDecls`, not `declsOf prog`** (L195). `--assn` reports about the
        -- *prelude-booted* model — that is the heap the difftest SUT runs and the one
        -- `heapOkB` certifies — so the table it reports against is the prelude-aware
        -- one, whose extra row is `T`. `--check` keeps `declsOf prog`, because
        -- `check_sound` is a statement about `Machine.init p` at the bare boot heap
        -- where `T` does not exist. Two tables, each sound at the heap it describes;
        -- see `Types/Decls.lean`'s `preludeDecls`.
        let D := Types.preludeDecls
        -- `--assn-top`: report the **top-level program** as one more body, under
        -- `Object#<main>`. `bodyReports` walks *into* structure and reports only
        -- `def`/`defs`, so a program's straight-line code — the part a reader is
        -- most likely to have an obvious type in mind for — has no row at all
        -- today, and the only verdict covering it is `--check`'s whole-program one.
        --
        -- **Off by default**, because `--assn`'s census is a consumed number
        -- (`homebrew/fragment-gap.py`'s third ratchet) and a body that is not a
        -- method body would move it.
        let rs := Types.bodyReports D "Object" prog ++
          (if args.contains "--assn-top" then
            [("Object", "<main>", Types.bodyVerdict D "Object" "<main>" prog)]
           else [])
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
      if assnProgOnly then
        -- `preludeDecls` for `--assn`'s reason (L195): this reports about the
        -- prelude-booted model, which is the heap the difftest SUT runs.
        let renderClass := fun (e : String × Types.TyVar × Option Types.TyVar) =>
          Lean.Json.mkObj [
            ("class", Lean.Json.str e.1),
            ("instance_var", Lean.Json.num e.2.1),
            ("class_object_var", match e.2.2 with
              | some β => Lean.Json.num β
              | none => Lean.Json.null)]
        IO.println (match Types.programVerdict Types.preludeDecls prog with
          | .acceptedUnder τ A cs consts =>
            Lean.Json.mkObj [
              ("status", Lean.Json.str "accept"),
              ("means", Lean.Json.str "types under these class obligations"),
              ("type", Lean.Json.str τ.render),
              ("assn", Lean.Json.str A.render),
              ("classes", Lean.Json.arr (cs.map renderClass).toArray),
              -- The class names this program *defines*, added to the constant table so
              -- the class object is a value (L264). Reported because it is a table
              -- extension, and an extension a reader cannot see is one they cannot
              -- check.
              ("consts_added", Lean.Json.arr (consts.map Lean.Json.str).toArray)]
          | .blocked τ n ps =>
            Lean.Json.mkObj [
              ("status", Lean.Json.str "unknown"),
              ("needed", Lean.Json.str
                (τ.render ++ " ~ " ++ n ++ " : (" ++
                  String.intercalate ", " (ps.map Types.ATy.render) ++ ") → _"))]
          | .outOfFragment head =>
            Lean.Json.mkObj [
              ("status", Lean.Json.str "unknown"),
              ("out_of_fragment", Lean.Json.str head)]).compress
        return 0
      if certifyJFile.isSome then
        let path := certifyJFile.getD ""
        let contents ← (do
          try
            let s ← IO.FS.readFile path
            pure (Except.ok s)
          catch e => pure (Except.error (toString e)))
        let out : Lean.Json :=
          match contents with
          | .error e =>
            Lean.Json.mkObj [("status", Lean.Json.str "reject"),
                             ("why", Lean.Json.str "certificate-unreadable"),
                             ("detail", Lean.Json.str e)]
          | .ok text =>
            match Lean.Json.parse text with
            | .error e =>
              Lean.Json.mkObj [("status", Lean.Json.str "reject"),
                               ("why", Lean.Json.str "certificate-bad-json"),
                               ("detail", Lean.Json.str e)]
            | .ok cj =>
              match Judgment.JCert.ofJson cj with
              | .error e =>
                Lean.Json.mkObj [("status", Lean.Json.str "reject"),
                                 ("why", Lean.Json.str "certificate-undecodable"),
                                 ("detail", Lean.Json.str e)]
              | .ok cert =>
                -- The fuel bounds two structural walks (the fragment scan and the
                -- derivation); any value past their depths is inert, and the walks
                -- are linear, so a large constant is safe and total.
                if Judgment.validateJ cert prog 1_000_000 then
                  Lean.Json.mkObj [("status", Lean.Json.str "accept"),
                    ("theorem", Lean.Json.str "validateJ_certifies"),
                    ("unconditional", Lean.Json.bool cert.deltaRows.isEmpty),
                    ("carries", Lean.Json.arr
                      (cert.deltaRows.map Cert.rowClaimToJson).toArray)]
                else
                  Lean.Json.mkObj [("status", Lean.Json.str "reject"),
                                   ("why", Lean.Json.str "validateJ-false")]
        IO.println out.compress
        return 0
      if certifyFile.isSome then
        let path := certifyFile.getD ""
        -- A missing or malformed certificate is a **reject**, not a crash: §1's
        -- "a bad certificate costs a body we failed to certify, never a false
        -- type-checked". The reason is reported, as `--assn`'s `needed` is.
        let contents ← (do
          try
            let s ← IO.FS.readFile path
            pure (Except.ok s)
          catch e => pure (Except.error (toString e)))
        let out : Lean.Json :=
          match contents with
          | .error e =>
            Lean.Json.mkObj [("status", Lean.Json.str "reject"),
                             ("why", Lean.Json.str "certificate-unreadable"),
                             ("detail", Lean.Json.str e)]
          | .ok text =>
            match Lean.Json.parse text with
            | .error e =>
              Lean.Json.mkObj [("status", Lean.Json.str "reject"),
                               ("why", Lean.Json.str "certificate-bad-json"),
                               ("detail", Lean.Json.str e)]
            | .ok cj =>
              match Cert.Cert.ofJson cj with
              | .error e =>
                Lean.Json.mkObj [("status", Lean.Json.str "reject"),
                                 ("why", Lean.Json.str "certificate-undecodable"),
                                 ("detail", Lean.Json.str e)]
              -- **V15's resolution step.** Claims travel as addresses and are
              -- checked against terms, so the path has to be resolved against
              -- *this* program before the validator sees the certificate. An
              -- address that names nothing is dropped, which refuses.
              | .ok cert => Cert.verdictToJson (Cert.Cert.resolveClaims prog cert) prog
        IO.println out.compress
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
        -- **`Types.tyName`, not a copy of it** (L193). This was an inline match on
        -- every `Ty` arm, which meant every new arm broke `Main.lean` and one of the
        -- two renderings drifted (`.cls n` here, `c` there — the same string, but
        -- nothing said so). One reader, one table: `tyName` is the printer's, and it
        -- is total by construction.
        let ty := match Types.infer (Types.declsOf prog) [] prog true with
          | some (t, _, _) => Types.tyName t
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
