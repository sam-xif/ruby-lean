import Ratchet.Validate

/-!
One rung of the ladder: real desugared Ruby (`program`, decoded straight from a
committed snapshot of `harness/desugar-dt/bin/export-json`'s output — see
`scripts/generate_corpus.py`; not re-derived live, so a rung's expected result cannot
silently change underneath it if the desugarer changes), a `Cert` claiming to type it,
and what `validate` is expected to say. There is deliberately no `expect_stuck` field:
the semantics *is* now run against the rungs the judgment covers, but by `Check13.lean`,
which derives the outcome by executing the program rather than reading a recorded
expectation from here (`AGENTS.md` §Semantics status).

**Every rung's target is `expect_validate = true` unless `falseReason` says otherwise.**
`falseReason` is `none` for the (overwhelming majority) case; when present, it is one
of three reasons a rung is honestly, permanently a `false` target rather than a bug to
fix:
- `"unsafe_program"` — the program really does reach a type-stuck outcome
  (`NoMethodError`/`ArgumentError`/`TypeError`) when run. No cert should ever certify
  it; a checker that did would be unsound.
- `"dishonest_cert"` — the program is safe, but *this specific certificate* makes a
  claim its own claimed facts don't support (e.g. a function's claimed return type
  doesn't match what its body actually computes). Rejecting it is a cert-consistency
  invariant, independent of whether some other, honest certificate for the same
  program would validate.
- `"cert_language_gap"` — the program is safe, but the current `Ty`/`Cert` grammar has
  no way to *state* a sufficient claim at all (not just "no rule for it yet" — see
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
  cert : Cert
  expectValidate : Bool
  falseReason : Option String

def CorpusEntry.ofJson? (j : Json) : Except String CorpusEntry := do
  let id ← j.getObjValAs? String "id"
  let tier ← j.getObjValAs? Nat "tier"
  let description ← j.getObjValAs? String "description"
  let program ← Decode.program (← j.getObjVal? "program")
  let cert ← Cert.ofJson? (← j.getObjVal? "cert")
  let expectValidate ← j.getObjValAs? Bool "expect_validate"
  let falseReason ← jOpt j "false_reason" Json.getStr?
  return { id, tier, description, program, cert, expectValidate, falseReason }

end Ratchet
