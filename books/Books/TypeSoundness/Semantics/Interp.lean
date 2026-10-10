import RubyCore.Interp
import RubyCore.Boot

/-!
The real semantics — **imported**, not copied, from the model (`RubyCore`, in the
`rubylean` package this one depends on). This is the one file that brings `stepFn`
into the soundness proof, and everything else in the book reaches the machine
through it.

Importing was chosen over hand-porting the way the checker's `Checker/Lang/Expr.lean`
and `Ty.lean` were. `stepFn`'s own dependency closure (`Heap`/`Machine`/`Builtins`/
`Builtins/*`/`CRubyNames`/`Interp/{Dispatch,Kont,Reflect,Send,Support}`) is on the
order of 24k lines, versus the ~450/~700 lines `Syntax.lean`/`Sorbet/Ty.lean` were.
Hand-copying that would mean maintaining a second, silently-driftable copy of the
model's entire runtime; importing it means the proof is always about whatever
`RubyCore/` — the real, differentially tested model — actually does.

The checker is the other way round: `Checker/` imports nothing from `RubyCore/`
(`books/scripts/check-isolation.sh` fails if it ever does), so that it can be read
and re-implemented without the model in scope. The namespace here is
`Checker.Semantics` only so that the proofs, which live under `Checker.Soundness`,
can write `Semantics.run`.

`typeStuck` is **restated**, not imported from `RubyCore.Proof.TypeSafety`
(`Books/Metatheory/Reachability/TypeSafety.lean`). It is defined here directly over the
real `RubyCore.isA` and `RubyCore.Boot.*ErrorId`, so it is the same *definition*, and
the headline theorem's statement can be read without the metatheory that proves
things about it.
-/

namespace Checker.Semantics

open RubyCore

/-- `NoMethodError ∪ ArgumentError ∪ TypeError`, closed under subclassing — the
bad-state family `typeStuck` is built from (mirrors the real
`RubyCore.Proof.TypeSafety.typeErrorFamily`). -/
def typeErrorFamily : List ObjId :=
  [Boot.noMethodErrorId, Boot.argumentErrorId, Boot.typeErrorId]

def isTypeError (h : Heap) (exc : Value) : Bool :=
  typeErrorFamily.any (isA h exc)

/-- Did this run's outcome land on a type error? Mirrors the real
`RubyCore.Proof.TypeSafety.typeStuck`, restated over `Interp.RunResult` (the fuel-loop
outcome) rather than the per-step `StepResult`, since that's what running a whole corpus
rung to completion actually produces. -/
def typeStuck : Interp.RunResult → Bool
  | .uncaught exc m => isTypeError m.heap exc
  | _ => false

/-- The machine after **booting the prelude** — RubyCore's core library written *in RubyCore*
(Enumerable/Comparable/Range). Computed once: a nullary `def` is a closed term, so the
compiler initialises it a single time rather than per rung, which matters because the boot
itself costs `PreludeBoot.bootFuel` steps.

**Corrected at tier 9c, and the correction is the finding.** This function used to be
`Interp.run fuel (Machine.init p)`, whose docstring claimed it ran "the same `Machine.init`
the real `rubycore` executable and the difftest engine use". That was wrong: the difftest
SUT boots the prelude (`PreludeBoot.initWithPrelude`), and `Machine.init` does not — so the
cross-check was running rungs against a *smaller* model than the agreement gate. It went
unnoticed for eleven clinks because nothing below tier 9c reached a prelude-defined method;
`Array#select` and `Array#sort_by` are the first, and `checkrungs` reported them as
`unsupported(unmodeled method Array#select)` while `run_agreement.sh` reported 136/136
agree. Two numbers disagreeing about the same model is exactly what the two-legged design is
supposed to surface, and it did. -/
def bootedMachine : Except String Machine := Prelude.boot

/-- Run a program to completion (or until fuel runs out) from the **prelude-booted** heap —
the same heap the difftest engine's `--sut lean` uses, so a rung runs against the *actual*
core library, not a reimplementation of it and not a subset of it.

A boot failure is reported as `unsupported` rather than silently falling back to the
unbooted heap: a cross-check against the wrong heap is worse than no cross-check. -/
def run (fuel : Nat) (p : Expr) : Interp.RunResult :=
  match bootedMachine with
  | .ok mp =>
    -- Mirrors `Prelude.initWithPrelude`'s heap and globals, spelled out so the `boot`
    -- result is shared across every rung in a run rather than recomputed per rung. The
    -- require/require_relative fixture overlay and the numeric-literal table that
    -- `initWithPrelude` also installs are omitted here: no corpus rung reads them.
    Interp.run fuel { Machine.initOn mp.heap p with globals := mp.globals }
  | .error msg => .unsupported s!"prelude boot failed: {msg}" (Machine.init p)

/-- Which outcome a run landed on, for a report line. -/
def outcomeLabel : Interp.RunResult → String
  | .value .. => "value"
  | .uncaught .. => "uncaught"
  | .unsupported r _ => s!"unsupported({r})"
  | .outOfFuel _ => "outOfFuel"
  | .stuck msg _ => s!"stuck({msg})"

/-- The Ruby class name of the value a run produced, or `none` if it did not produce
one. `realClassOf`, not `classOf`: this is what `Object#class` reports (it skips the
eigenclass), which is the thing a type is a claim about.

Deliberately returns a `String`, not a `Checker.Ty`: `Books/TypeSoundness/Semantics/` stays free of any
dependency on `Checker/`'s copied type language (`AGENTS.md` §Isolation — the arrow only
ever points `Books/TypeSoundness/Semantics/ → RubyCore/`). Mapping a class name back to a `Ty` is the
cross-checker's job, at the one place that is allowed to see both (`Check13.lean`). -/
def resultClassName : Interp.RunResult → Option String
  | .value v m => some (className m.heap (realClassOf m.heap v))
  | _ => none

end Checker.Semantics
