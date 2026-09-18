import Ratchet.Check.Check
import Ratchet.Lang.Expr

/-!
One rung of the **typed** ladder, as `scripts/build_corpus.py` leaves it in `build/`.

This is the replacement for `Ratchet/Corpus.lean`'s `CorpusEntry`, and the difference is
the whole reshaping in one field: a rung no longer carries only a program and a target,
it carries a **derivation**, emitted from Sorbet's answer about the annotated source and
checked here against the sig-stripped program. `AGENTS.md` §Claim-free still holds and is
*why* the derivation is safe to carry: the checker believes none of it -- every type in a
`Deriv` is re-derived, so a certificate is a hint about where to look, not a claim to
trust (`Ratchet/Check/Deriv.lean`'s header; `sorbet-cert/README.md` §3's tamper control).

Four stages upstream of this file are untrusted and may each fail in a way worth
reporting rather than crashing on, so the record is deliberately partial: `program`
and `deriv` are `Option`, and `emitBlocked` carries the emitter's named reason.
-/

namespace Ratchet

-- `Json` is this project's vendored copy of Lean's (`Json.lean`), at the root
-- namespace, so there is nothing to open.

/-- What happened to a rung on the way here. Every constructor except `ok` is a
measurement: a stage that declined, with the reason it gave. -/
inductive RungStage where
  /-- `srb`, the strip stack, `export-json` and the emitter all completed. -/
  | ok
  /-- The emitter declined; `why` names the fragment boundary it hit. -/
  | blocked (why : String)
  /-- An upstream stage errored (`srb` missing, a strip transform, the desugarer). -/
  | failed (stage why : String)
deriving Repr, Inhabited

structure Rung where
  base : String
  id : String
  tier : Nat
  description : String
  /-- Did `srb` typecheck the **annotated** source clean? -/
  srbClean : Bool
  /-- Is it expected to? A rung whose program is genuinely ill-typed should be caught
      by Sorbet too, and a disagreement here is a finding about one of the two. -/
  expectSorbet : Bool
  /-- How many signatures `srb` resolved into `Ty`, and how many it could not. The
      second number is the measurement that drives the annotation work. -/
  sigs : Nat
  dropped : List String
  stage : RungStage
  /-- The **sig-stripped** program -- the one the certificate is about. -/
  program : Option Expr
  deriv : Option Deriv
  expectValidate : Bool
  falseReason : Option String
  /-- A stage *before* the emitter that is recorded as declining -- today the eleven
      `slice/` rungs whose whole-file sources `difftest/ruby/sig_strip.rb` cannot strip.
      Recorded (`scripts/record_baseline.py`) so that a **new** upstream failure is red
      while a known one is a number. -/
  knownUpstreamFailure : Option String
deriving Inhabited

def Rung.ofJson? (j : Json) : Except String Rung := do
  let base ← j.getObjValAs? String "base"
  let id ← j.getObjValAs? String "id"
  let tier ← j.getObjValAs? Nat "tier"
  let description ← j.getObjValAs? String "description"
  let expectValidate ← j.getObjValAs? Bool "expect_validate"
  let expectSorbet ← j.getObjValAs? Bool "expect_sorbet"
  let falseReason ← jOpt j "false_reason" Json.getStr?
  let srbClean := (j.getObjValAs? Bool "srb_clean").toOption.getD false
  let sigs := (j.getObjValAs? Nat "sigs").toOption.getD 0
  let dropped ← match jList j "dropped" (fun d => d.getObjValAs? String "why") with
    | .ok ds => pure ds
    | .error _ => pure []
  let knownUpstreamFailure ← jOpt j "known_upstream_failure" Json.getStr?
  let program ← jOpt j "program" (fun p => Decode.program p)
  let stageName := (j.getObjValAs? String "stage").toOption.getD "?"
  let mut stage : RungStage := .failed stageName
    ((j.getObjValAs? String "error").toOption.getD "")
  let mut deriv : Option Deriv := none
  if stageName == "done" then
    let emit ← j.getObjVal? "emit"
    match (emit.getObjValAs? String "status").toOption.getD "?" with
    | "ok" =>
      let d ← Deriv.ofJson? (← emit.getObjVal? "deriv")
      stage := .ok
      deriv := some d
    | "blocked" =>
      stage := .blocked ((emit.getObjValAs? String "why").toOption.getD "?")
    | other => stage := .failed "emit" s!"unknown status '{other}'"
  return { base, id, tier, description, srbClean, expectSorbet, sigs, dropped,
           stage, program, deriv, expectValidate, falseReason, knownUpstreamFailure }

/-- A rung's verdict: `validateD` on the pair, or `false` for any rung that never got a
program and a derivation to check. A blocked rung is **not** an accept, and the report
keeps the two apart so that "not yet in the fragment" never reads as "certified". -/
def Rung.verdict (r : Rung) : Bool :=
  match r.program, r.deriv with
  | some p, some d => validateD p d
  | _, _ => false

end Ratchet
