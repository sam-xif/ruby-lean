import Ratchet.Controls.CallbackBodyCheckControls

/-! Complete source acceptance and adversarial callback certificates. Signatures come
from independently checked definitions; source code, live captures and later contexts matter. -/
namespace Ratchet.CallbackCallControls
open CallbackBodyCheckControls

private def blockBody (name : String) : Expr := .send (some (.var .lvar name)) "*" [.int 10] none
private def blockHint (name : String) : Deriv := .prim (.var .lvar name) "*" [.intLit 10] .int .int
private def definition := Expr.def' "twice" [] twice
private def call (ps : List Param) (body : Expr) : Expr := .send none "twice" [] (some (.block ps [] body))
private def program (body : Expr) : Expr := .seq [definition, call [.req "x"] body]
private def certificate (body : Deriv) : Deriv := .flow (.seq [hint, .callBlock "twice" body .int])

#guard validateD (program (blockBody "x")) (certificate (blockHint "x"))
#guard validateD (.seq [definition, call [.req "renamed"] (blockBody "renamed")])
  (certificate (blockHint "renamed"))
#guard !(validateD (program (blockBody "x")) (certificate (blockHint "forged")))
#guard !(validateD (program (blockBody "x")) (certificate (.prim (.var .lvar "x") "*" [.intLit 11] .int .int)))
#guard !(validateD (program (.str "bad")) (certificate (.strLit "bad")))
#guard !(validateD (program .nil) (certificate .nilLit))
#guard !(validateD (call [.req "x"] (blockBody "x")) (.flow (.callBlock "twice" (blockHint "x") .int)))
#guard !(validateD (program (blockBody "x")) (.flow (.seq [hint, .callBlock "other" (blockHint "x") .int])))
#guard !(validateD (program (blockBody "x")) (.flow (.seq [hint, .callBlock "twice" (blockHint "x") .bool])))
#guard !(validateD (.seq [definition, call [] (.int 1)]) (certificate (.intLit 1)))
#guard !(validateD (.seq [definition, call [.req "x", .req "extra"] (blockBody "x")])
  (certificate (blockHint "x")))
#guard !(validateD (.seq [definition, .send none "twice" [.int 0] (some (.block [.req "x"] [] (blockBody "x")))])
  (certificate (blockHint "x")))

private def writeBody : Expr := .vasgn .lvar "total" (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
private def writeHint : Deriv := .vasgn .lvar "total" (.prim (.var .lvar "total") "+" [.var .lvar "x"] .int .int)
private def mixedDef := Expr.def' "mixed" [] mixed
private def mixedDefHint := Deriv.defBlock "mixed" [] [.int] .int .int mixedHint
private def writeProgram (body : Expr) : Expr := .seq [mixedDef, .vasgn .lvar "total" (.int 0),
  .send none "mixed" [] (some (.block [.req "x"] [] body)), .var .lvar "total"]
private def writeCertificate (body : Deriv) : Deriv := .flow (.seq [mixedDefHint, .vasgn .lvar "total" (.intLit 0),
  .callBlock "mixed" body .int, .var .lvar "total"])
#guard validateD (writeProgram writeBody) (writeCertificate writeHint)
-- An Integer result does not hide a captured type change earlier in the block.
#guard !(validateD (writeProgram (.seq [.vasgn .lvar "total" .nil, .int 1]))
  (writeCertificate (.seq [.vasgn .lvar "total" .nilLit, .intLit 1])))

-- A later declaration changes the exact context and rechecks the saved body.
private def laterDef := Expr.def' "later" [] (.int 7)
private def laterHint := Deriv.defDecl "later" [] .int (.intLit 7)
#guard validateD (.seq [definition, laterDef, call [.req "x"] (blockBody "x")])
  (.flow (.seq [hint, laterHint, .callBlock "twice" (blockHint "x") .int]))
private def checkedDef := (check 60 [] definition hint).get (by decide)
#guard (refreshCallbackBodies 40 checkedDef.ctx .ivar0 checkedDef.cache.callbacks).isSome
#guard (refreshCallbackBodies 40 (reserveNameCtx checkedDef.ctx "+") .ivar0 checkedDef.cache.callbacks).isNone
#guard (findCallback checkedDef.ctx .ivar0 "twice" checkedDef.cache.callbacks).isSome
#guard (findCallback (reserveNameCtx checkedDef.ctx "other") .ivar0 "twice" checkedDef.cache.callbacks).isNone
#guard !(cacheSignaturesB checkedDef.cache {})

private def namedProgram (name : String) := Expr.seq [.def' name [] twice,
  .send none name [] (some (.block [.req "x"] [] (blockBody "x")))]
private def namedHint (name : String) := Deriv.flow (.seq [
  .defBlock name [] [.int] .int .int twiceHint, .callBlock name (blockHint "x") .int])
#guard validateD (namedProgram "lambda") (namedHint "lambda")
#guard validateD (namedProgram "proc") (namedHint "proc")
#guard validateD (namedProgram "new") (namedHint "new")

#guard ((Json.parse "{\"rule\":\"callBlock\",\"name\":\"twice\",\"body\":{\"rule\":\"intLit\",\"n\":1},\"ret\":{\"tag\":\"int\"}}").bind Deriv.ofJson?).isOk
end Ratchet.CallbackCallControls
