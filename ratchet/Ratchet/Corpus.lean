import Ratchet.Validate

/-!
One rung of the ladder: real desugared Ruby (`program`, decoded straight from a
committed snapshot of `harness/desugar-dt/bin/export-json`'s output — see
`scripts/generate_corpus.py`; not re-derived live, so a rung's expected result cannot
silently change underneath it if the desugarer changes) and what `validate` is expected
to say. There is no certificate: a rung is just a program and a target, and `validate`
must synthesize or fail (`AGENTS.md` §Claim-free). There is deliberately no `expect_stuck` field:
the semantics *is* now run against the rungs the judgment covers, but by `Check13.lean`,
which derives the outcome by executing the program rather than reading a recorded
expectation from here (`AGENTS.md` §Semantics status).

**Every rung's target is `expect_validate = true` unless `falseReason` says otherwise.**
`falseReason` is `none` for the (overwhelming majority) case; when present, it is one
of two reasons a rung is honestly, permanently a `false` target rather than a bug to
fix:
- `"unsafe_program"` — the program really does reach a type-stuck outcome
  (`NoMethodError`/`ArgumentError`/`TypeError`) when run. A checker that said `true`
  here would be unsound.
- `"ty_language_gap"` — the program is safe, but the current `Ty` grammar has no value
  that *describes* the type in question at all (not just "no rule for it yet" — see
  `Ratchet/Ty.lean`'s constructors). This is the one worth watching: it names a
  concrete extension `Ty` needs, not a `chk` rule to write.
-/

namespace Ratchet

open Lean (Json)

structure CorpusEntry where
  id : String
  tier : Nat
  description : String
  program : Expr
  expectValidate : Bool
  falseReason : Option String

def CorpusEntry.ofJson? (j : Json) : Except String CorpusEntry := do
  let id ← j.getObjValAs? String "id"
  let tier ← j.getObjValAs? Nat "tier"
  let description ← j.getObjValAs? String "description"
  let program ← Decode.program (← j.getObjVal? "program")
  let expectValidate ← j.getObjValAs? Bool "expect_validate"
  let falseReason ← jOpt j "false_reason" Json.getStr?
  return { id, tier, description, program, expectValidate, falseReason }

end Ratchet
