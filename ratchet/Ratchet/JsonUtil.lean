import Lean.Data.Json

/-!
Small hand-written JSON decode helpers, shared by every `ofJson?` in this
package. We decode manually rather than `deriving FromJson` so the wire
format is a stable, uniform `{"tag": ..., <named fields>}` shape that a
Python corpus generator can also emit by hand without reverse-engineering
Lean's derive conventions.
-/

namespace Ratchet

open Lean (Json)

/-- The JSON array at key `k`, still as raw `Json` values. -/
def jArr (j : Json) (k : String) : Except String (List Json) := do
  let v ← j.getObjVal? k
  let a ← v.getArr?
  return a.toList

/-- Decode the array at key `k` by mapping `f` over each element. -/
def jList (j : Json) (k : String) (f : Json → Except String α) : Except String (List α) := do
  let js ← jArr j k
  js.mapM f

/-- Decode an optional field: missing or `null` becomes `none`. -/
def jOpt (j : Json) (k : String) (f : Json → Except String α) : Except String (Option α) :=
  match j.getObjValD k with
  | Json.null => pure none
  | other => return some (← f other)

end Ratchet
