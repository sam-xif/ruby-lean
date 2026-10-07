import Checker.Controls.BoundBodyCheckControls

/-! Full admission and hostile hints: definitions, aliases, live captures and cache
refresh all cross validateD. A good callback cannot rescue a bad declared method domain. -/
namespace Checker.BoundCallControls
open BoundBodyCheckControls

def definition : Expr := .def' "run" [.block (some "b")] (call "b" 5)
def definitionHint : Deriv := hint (callHint "b" 5)
def block (x : String) : Expr := .send (some (.var .lvar x)) "+" [.int 1] none
def blockHint (x : String) : Deriv := .prim (.var .lvar x) "+" [.intLit 1] .int .int
def sourceCall (ps : List Param) (e : Expr) : Expr := .send none "run" [] (some (.block ps [] e))
def program (e : Expr) : Expr := .seq [definition, sourceCall [.req "x"] e]
def certificate (d : Deriv) : Deriv := .flow (.seq [definitionHint, .callBlock "run" d .int])

#guard validateD (program (block "x")) (certificate (blockHint "x"))
#guard validateD (.seq [definition, sourceCall [.req "renamed"] (block "renamed")]) (certificate (blockHint "renamed"))
#guard !(validateD (program (block "x")) (certificate (blockHint "forged")))
#guard !(validateD (program .nil) (certificate .nilLit))
#guard !(validateD (sourceCall [.req "x"] (block "x")) (.flow (.callBlock "run" (blockHint "x") .int)))
#guard !(validateD (.seq [definition, sourceCall [] (.int 1)]) (certificate (.intLit 1)))
#guard !(validateD (.seq [definition, sourceCall [.req "x", .req "extra"] (block "x")]) (certificate (blockHint "x")))
#guard !(validateD (.seq [definition, .send none "run" [.int 0] (some (.block [.req "x"] [] (block "x")))])
  (certificate (blockHint "x")))
#guard !(validateD (program (block "x")) (.flow (.seq [
  hint (callHint "b" 5) [.cls "String"], .callBlock "run" (blockHint "x") .int])))

def aliasBody : Expr := .seq [.vasgn .lvar "copy" (.var .lvar "b"), .vasgn .lvar "b" .nil,
  call "copy" 5, .vasgn .lvar "copy" .nil, .yield' [.int 7]]
def aliasHint : Deriv := .seq [.vasgn .lvar "copy" (.var .lvar "b"), .vasgn .lvar "b" .nilLit,
  callHint "copy" 5, .vasgn .lvar "copy" .nilLit, .yieldArgs [.intLit 7]]
def writeBody : Expr := .vasgn .lvar "total" (.send (some (.var .lvar "total")) "+" [.var .lvar "value"] none)
def writeHint : Deriv := .vasgn .lvar "total" (.prim (.var .lvar "total") "+" [.var .lvar "value"] .int .int)
def writeProgram (e : Expr) : Expr := .seq [.def' "run" [.block (some "b")] aliasBody,
  .vasgn .lvar "total" (.int 0), sourceCall [.req "value"] e, .var .lvar "total"]
def writeCertificate (d : Deriv) : Deriv := .flow (.seq [hint aliasHint,
  .vasgn .lvar "total" (.intLit 0), .callBlock "run" d .int, .var .lvar "total"])
#guard validateD (writeProgram writeBody) (writeCertificate writeHint)
#guard !(validateD (writeProgram (.seq [.vasgn .lvar "total" .nil, .int 1]))
  (writeCertificate (.seq [.vasgn .lvar "total" .nilLit, .intLit 1])))

private def checked := (Checker.check 80 [] definition definitionHint).get (by decide)
#guard (refreshBoundCallbackBodies 50 checked.ctx .ivar0 checked.cache.boundCallbacks).isSome
#guard (refreshBoundCallbackBodies 50 (reserveNameCtx checked.ctx "call") .ivar0 checked.cache.boundCallbacks).isNone
#guard (findBoundCallback checked.ctx .ivar0 "run" checked.cache.boundCallbacks).isSome
#guard (findBoundCallback (reserveNameCtx checked.ctx "other") .ivar0 "run" checked.cache.boundCallbacks).isNone
#guard !(cacheSignaturesB checked.cache {})
#guard validateD (.seq [definition, .def' "later" [] (.int 7), sourceCall [.req "x"] (block "x")])
  (.flow (.seq [definitionHint, .defDecl "later" [] .int (.intLit 7), .callBlock "run" (blockHint "x") .int]))

private def unused (bs : List Ty) := (Checker.check 80 [] (.def' "run" [.block (some "b")] (.int 5))
  (hint (.intLit 5) bs)).map (·.cache)
#guard !(cacheSignaturesB ((unused [.int]).get (by decide)) ((unused [.cls "String"]).get (by decide)))

private def named (name : String) := Expr.seq [.def' name [.block (some "b")] (call "b" 5),
  .send none name [] (some (.block [.req "x"] [] (block "x")))]
private def namedHint (name : String) := Deriv.flow (.seq [
  .defBlock name [] [.int] .int .int (callHint "b" 5), .callBlock name (blockHint "x") .int])
#guard validateD (named "lambda") (namedHint "lambda")
#guard validateD (named "proc") (namedHint "proc")
#guard validateD (named "new") (namedHint "new")
end Checker.BoundCallControls
