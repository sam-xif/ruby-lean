import Ratchet.Validate

/-!
One rung of the ladder: real desugared Ruby (`program`, decoded straight from a
committed snapshot of `harness/desugar-dt/bin/export-json`'s output — see
`scripts/generate_corpus.py`; not re-derived live, so a rung's expected result cannot
silently change underneath it if the desugarer changes), a `Cert` claiming to type it,
and what `validate` is expected to say. There is no `expect_stuck`/`frontier` pairing
yet (contrast the previous, now-replaced hand-authored-AST corpus): with no semantics
ported yet (`AGENTS.md`), there is nothing to run a rung against besides `validate`
itself.
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

def CorpusEntry.ofJson? (j : Json) : Except String CorpusEntry := do
  let id ← j.getObjValAs? String "id"
  let tier ← j.getObjValAs? Nat "tier"
  let description ← j.getObjValAs? String "description"
  let program ← Decode.program (← j.getObjVal? "program")
  let cert ← Cert.ofJson? (← j.getObjVal? "cert")
  let expectValidate ← j.getObjValAs? Bool "expect_validate"
  return { id, tier, description, program, cert, expectValidate }

end Ratchet
