import Books.TypeSoundness.Checker.Check.CheckCallbackBody
import Books.TypeSoundness.Checker.Check.Check

/-! Definition-side checks run without any caller. Forged signatures and source hints
cannot turn a bad body into a derivation; ordinary fallback cannot swallow a yield. -/
namespace Checker.CallbackBodyCheckControls

def twice : Expr := .send (some (.yield' [.int 1])) "+" [.yield' [.int 2]] none
def twiceHint : Deriv := .prim (.yieldArgs [.intLit 1]) "+" [.yieldArgs [.intLit 2]] .int .int
def decl : Defn := ⟨"twice", [], twice⟩
def hint : Deriv := .defBlock "twice" [] [.int] .int .int twiceHint
def checked : CheckedCallbackBody ctx0 .ivar0 decl :=
  (checkCallbackBody 30 ctx0 .ivar0 decl hint).get (by decide)

#guard checked.params == [] && checked.blockArgs == [.int] && checked.blockRet == .int
#guard checked.ret == .int && checked.out == []

private def expr (e : Expr) (d : Deriv) :=
  checkCallbackExpr 40 ctx0 .ivar0 ⟨"Object", "Object", "twice", false⟩ [.int] .int [] e d

-- The certificate is still required to describe the exact source and inferred types.
#guard (expr twice (.prim (.yieldArgs [.intLit 9]) "+" [.yieldArgs [.intLit 2]] .int .int)).isNone
#guard (expr twice (.prim (.yieldArgs [.intLit 1]) "-" [.yieldArgs [.intLit 2]] .int .int)).isNone
#guard (expr twice (.prim (.yieldArgs [.intLit 1]) "+" [.yieldArgs [.intLit 2]] .nilT .int)).isNone
#guard (expr twice (.prim (.yieldArgs [.intLit 1]) "+" [.yieldArgs [.intLit 2]] .int .nilT)).isNone
#guard (expr twice (.prim (.yieldArgs []) "+" [.yieldArgs [.intLit 2]] .int .int)).isNone
#guard (expr (.yield' [.nil]) (.yieldArgs [.nilLit])).isNone
#guard (expr (.yield' [.int 1, .int 2]) (.yieldArgs [.intLit 1, .intLit 2])).isNone
#guard (expr (.yield' [.splat (some (.array [.int 1]))]) (.yieldArgs [.arrayLit [.intLit 1] .int])).isNone
#guard (checkCallbackExpr 0 ctx0 .ivar0 ⟨"Object", "Object", "twice", false⟩ [.int] .int [] twice twiceHint).isNone

private def defHint (name : String) (ps : List SigParam) (bs : List Ty) (br ret : Ty) : Deriv :=
  .defBlock name ps bs br ret twiceHint
#guard (checkCallbackBody 30 ctx0 .ivar0 decl (defHint "other" [] [.int] .int .int)).isNone
#guard (checkCallbackBody 30 ctx0 .ivar0 decl (defHint "twice" [("x", .int)] [.int] .int .int)).isNone
#guard (checkCallbackBody 30 ctx0 .ivar0 decl (defHint "twice" [] [.nilT] .int .int)).isNone
#guard (checkCallbackBody 30 ctx0 .ivar0 decl (defHint "twice" [] [.int] (.cls "String") .int)).isNone
#guard (checkCallbackBody 30 ctx0 .ivar0 decl (defHint "twice" [] [.int] .int (.cls "String"))).isNone
#guard (checkCallbackBody 30 ctx0 .ivar0 decl (.defDecl "twice" [] .int twiceHint)).isNone
-- Explicit &b entry/binding is not claimed by this required-positional body artifact.
#guard (checkCallbackBody 30 ctx0 .ivar0 { decl with params := [.block (some "b")] } hint).isNone

private def relay : Defn := ⟨"relay", [.req "value"], .yield' [.var .lvar "value"]⟩
private def relayHint (name : String) (ty : Ty) : Deriv :=
  .defBlock "relay" [(name, ty)] [.int] .int .int (.yieldArgs [.var .lvar "value"])
#guard (checkCallbackBody 30 ctx0 .ivar0 relay (relayHint "value" .int)).isSome
#guard (checkCallbackBody 30 ctx0 .ivar0 relay (relayHint "value" (.nilable .int))).isNone
#guard (checkCallbackBody 30 ctx0 .ivar0 relay (relayHint "renamed" .int)).isNone
#guard (checkCallbackBody 30 ctx0 .ivar0 relay (relayHint "value" (.sameAs "caller" .int))).isNone

private def localWrite (e : Expr) : Expr := .vasgn .lvar "total" e
private def localHint (d : Deriv) : Deriv := .vasgn .lvar "total" d
def mixed : Expr := .seq [localWrite .nil, localWrite (.yield' [.int 1]),
  .vasgn .lvar "result" (.yield' [.int 2]),
  .send (some (.var .lvar "total")) "+" [.var .lvar "result"] none]
def mixedHint : Deriv := .seq [localHint .nilLit, localHint (.yieldArgs [.intLit 1]),
  .vasgn .lvar "result" (.yieldArgs [.intLit 2]),
  .prim (.var .lvar "total") "+" [.var .lvar "result"] .int .int]
def mixedDecl : Defn := ⟨"mixed", [], mixed⟩
def mixedChecked : CheckedCallbackBody ctx0 .ivar0 mixedDecl :=
  (checkCallbackBody 40 ctx0 .ivar0 mixedDecl (.defBlock "mixed" [] [.int] .int .int mixedHint)).get (by decide)
#guard mixedChecked.out == [("total", .int), ("result", .int)]
#guard (expr (.yield' [localWrite (.yield' [.int 1])])
  (.yieldArgs [localHint (.yieldArgs [.intLit 1])])).isSome
#guard (expr (.seq [.int 1, .int 2]) (.seq [.intLit 1])).isNone
#guard (expr (localWrite (.int 1)) (.vasgn .lvar "other" (.intLit 1))).isNone

-- Saved arrays use an ordinary proof; an array element that yields lacks that proof.
#guard (expr (.send (some (.array [.int 10, .int 20])) "[]" [.yield' [.int 1]] none)
  (.prim (.arrayLit [.intLit 10, .intLit 20] .int) "[]" [.yieldArgs [.intLit 1]] (.arrayOf .int) (.nilable .int))).isSome
#guard (expr (.array [.yield' [.int 1]]) (.arrayLit [.yieldArgs [.intLit 1]] .int)).isNone
#guard (expr (.array [.int 1]) (.arrayLit [.intLit 1] .nilT)).isNone
#guard ((expr twice twiceHint).map (·.ordinary.isNone)) == some true
#guard ((expr (.array [.int 1]) (.arrayLit [.intLit 1] .int)).map (·.ordinary.isSome)) == some true

-- Wire hints decode; a checked uncalled definition is now admitted, while a bare yield is not.
private def wire := "{\"rule\":\"defBlock\",\"name\":\"twice\",\"params\":[],\"blockArgs\":[{\"tag\":\"int\"}],\"blockRet\":{\"tag\":\"int\"},\"ret\":{\"tag\":\"int\"},\"body\":{\"rule\":\"yield\",\"args\":[{\"rule\":\"intLit\",\"n\":1}]}}"
#guard ((Json.parse wire).bind Deriv.ofJson?).isOk
#guard validateD (.def' decl.name decl.params decl.body) hint
#guard !(validateD (.yield' [.int 1]) (.yieldArgs [.intLit 1]))

end Checker.CallbackBodyCheckControls
