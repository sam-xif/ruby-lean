import Ratchet.Check.CheckMethodFlow
import Ratchet.Check.Check

/-! Whole-definition checking without call values: actual source/hint agreement,
declared callback domains, copied identities, overwrites and saved receivers. -/
namespace Ratchet.BoundBodyCheckControls

def call (x : String) (n : Int) (selector : String := "call") : Expr :=
  .send (some (.var .lvar x)) selector [.int n] none
def callHint (x : String) (n : Int) : Deriv := .callbackCall (.var .lvar x) [.intLit n]
def decl (body : Expr) (localName : String := "b") : Defn := ⟨"run", [.block (some localName)], body⟩
def hint (body : Deriv) (bs : List Ty := [.int]) (br ret : Ty := .int) : Deriv :=
  .defBlock "run" [] bs br ret body
def check (body : Expr) (d : Deriv) := checkBoundCallbackBody 40 ctx0 .ivar0 (decl body) (hint d)

def directChecked := (check (call "b" 5) (callHint "b" 5)).get (by decide)
#guard directChecked.localName == "b" && directChecked.blockArgs == [.int] && directChecked.ret == .int
#guard (check (call "b" 5 "[]") (callHint "b" 5)).isSome
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 (decl (call "renamed" 5) "renamed")
  (hint (callHint "renamed" 5))).isSome

def copiedBody : Expr := .seq [.vasgn .lvar "copy" (.var .lvar "b"), .vasgn .lvar "b" .nil,
  call "copy" 5, call "copy" 7]
def copiedHint : Deriv := .seq [.vasgn .lvar "copy" (.var .lvar "b"), .vasgn .lvar "b" .nilLit,
  callHint "copy" 5, callHint "copy" 7]
def copiedChecked := (check copiedBody copiedHint).get (by decide)
#guard copiedChecked.out == [("b", .fixed .nilT), ("copy", .callback)]
#guard copiedChecked.outFacts.aliases == ["copy"]

def restoredBody : Expr := .seq [.vasgn .lvar "copy" (.var .lvar "b"), .vasgn .lvar "b" .nil,
  .vasgn .lvar "b" (.var .lvar "copy"), call "b" 5]
def restoredHint : Deriv := .seq [.vasgn .lvar "copy" (.var .lvar "b"), .vasgn .lvar "b" .nilLit,
  .vasgn .lvar "b" (.var .lvar "copy"), callHint "b" 5]
def restoredChecked := (check restoredBody restoredHint).get (by decide)

def receiverBody : Expr := .send (some (.seq [.vasgn .lvar "copy" (.var .lvar "b"),
  .vasgn .lvar "b" .nil, .var .lvar "copy"])) "call" [.int 5] none
def receiverHint : Deriv := .callbackCall (.seq [.vasgn .lvar "copy" (.var .lvar "b"),
  .vasgn .lvar "b" .nilLit, .var .lvar "copy"]) [.intLit 5]
def receiverChecked := (check receiverBody receiverHint).get (by decide)

def savedBody : Expr := .seq [.vasgn .lvar "copy" (.var .lvar "b"),
  .send (some (.var .lvar "b")) "call" [.seq [.vasgn .lvar "copy" .nil, .int 5]] none, call "b" 7]
def savedHint : Deriv := .seq [.vasgn .lvar "copy" (.var .lvar "b"),
  .callbackCall (.var .lvar "b") [.seq [.vasgn .lvar "copy" .nilLit, .intLit 5]], callHint "b" 7]
def savedChecked := (check savedBody savedHint).get (by decide)
#guard (check (.send (some (.var .lvar "b")) "call" [.seq [.vasgn .lvar "b" .nil, .int 5]] none)
  (.callbackCall (.var .lvar "b") [.seq [.vasgn .lvar "b" .nilLit, .intLit 5]])).isSome

-- Source mismatches, non-native selectors, missing bindings and overwritten receivers.
#guard (check (call "b" 5) (callHint "b" 9)).isNone
#guard (check (call "b" 5) (callHint "other" 5)).isNone
#guard (check (call "b" 5 "to_s") (callHint "b" 5)).isNone
#guard (check (call "unknown" 5) (callHint "unknown" 5)).isNone
#guard (check (.seq [.vasgn .lvar "b" .nil, call "b" 5])
  (.seq [.vasgn .lvar "b" .nilLit, callHint "b" 5])).isNone
#guard (check (.seq [.vasgn .lvar "copy" .nil, call "copy" 5])
  (.seq [.vasgn .lvar "copy" .nilLit, callHint "copy" 5])).isNone
#guard (check (.seq [.int 1, call "b" 5]) (.seq [callHint "b" 5])).isNone
#guard (check (.vasgn .lvar "x" (.int 1)) (.vasgn .lvar "y" (.intLit 1))).isNone
#guard (check (call "b" 5) (.callbackCall (.var .lvar "b") [])).isNone
#guard (check (.send (some (.var .lvar "b")) "call" [] none) (callHint "b" 5)).isNone

-- A definition is checked over the proposed signature before any callback is supplied.
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 (decl (call "b" 5))
  (hint (callHint "b" 5) [.nilT])).isNone
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 (decl (call "b" 5))
  (hint (callHint "b" 5) [.cls "String"])).isNone
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 (decl (call "b" 5))
  (hint (callHint "b" 5) [(.nilable .int)])).isNone
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 (decl (call "b" 5))
  (hint (callHint "b" 5) [.int] (.cls "String") .int)).isNone
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 (decl (call "b" 5))
  (hint (callHint "b" 5) [.int] .int .nilT)).isNone
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 (decl (call "b" 5))
  (.defBlock "wrong" [] [.int] .int .int (callHint "b" 5))).isNone
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 { decl (call "b" 5) with params := [] }
  (hint (callHint "b" 5))).isNone
#guard (checkBoundCallbackBody 40 ctx0 .ivar0 { decl (call "b" 5) with params := [.block none] }
  (hint (callHint "b" 5))).isNone
#guard (checkBoundCallbackBody 0 ctx0 .ivar0 (decl (call "b" 5)) (hint (callHint "b" 5))).isNone

-- The staged body family does not itself grant validateD admission.
#guard !(validateD (.def' "run" [.block (some "b")] (call "b" 5)) (hint (callHint "b" 5)))
private def wire := "{\"rule\":\"callbackCall\",\"recv\":{\"rule\":\"var\",\"kind\":\"lvar\",\"name\":\"b\"},\"args\":[{\"rule\":\"intLit\",\"n\":5}]}"
#guard ((Json.parse wire).bind Deriv.ofJson?).isOk

end Ratchet.BoundBodyCheckControls
