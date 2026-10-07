import Books.TypeSoundness.Examples.SuperDerivations
import Checker.Check.Check

/-! Whole-program super admission, argument effects and receiver-aware parent replay.
Bad uncalled overrides fail at definition time, before any constructor is requested. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.SuperCheckControls
open RubyCore Checker SuperProgram

def parentHint : Deriv := .classDecl "Shape" none (.seq [
  .defDecl "initialize" params .any (.ivarAsgn "@sides" (.var .lvar "sides")),
  .defDecl "sides" [] .int (.ivarRead "@sides" .int)])
def childHint (body : Deriv) : Deriv := .classDecl "Triangle" (some "Shape")
  (.defDecl "initialize" [] .any body)
def getHint (cn : String) (I : Ty) : Deriv :=
  .callMethodSig (.newInst cn [] (.inst cn I)) "sides" [] .int
def hint (args : List Deriv) : Deriv := .seq [parentHint, childHint (.superInit args), getHint "Triangle" fields]
def programArgs (args : List Checker.Expr) : Checker.Expr := .seq [parentExpr,
  .class' "Triangle" (some (.const "Shape")) (.def' "initialize" [] (.super' args none)), getExpr]

#guard validateD (program 3) (hint [.intLit 3])
#guard !validateD (program 3) (hint [.intLit 4])
#guard !validateD (programArgs []) (hint [])
#guard !validateD (programArgs [.int 3, .int 4]) (hint [.intLit 3, .intLit 4])
#guard !validateD (programArgs [.int 3]) (hint [])

def badUncalled : Checker.Expr := .seq [parentExpr,
  .class' "Triangle" (some (.const "Shape"))
    (.def' "initialize" [.req "flag"] (.super' [.var .lvar "flag"] none))]
#guard !validateD badUncalled (.seq [parentHint, .classDecl "Triangle" (some "Shape")
  (.defDecl "initialize" [("flag", .bool)] .any (.superInit [.var .lvar "flag"]))])

-- The current defining owner stays Triangle when a further subclass inherits its body.
def inherited : Checker.Expr := .seq [parentExpr, childExpr 5,
  .class' "Scalene" (some (.const "Triangle")) .nil,
  .send (some (.send (some (.const "Scalene")) "new" [] none)) "sides" [] none]
#guard validateD inherited (.seq [parentHint, childHint (.superInit [.intLit 5]),
  .classDecl "Scalene" (some "Triangle") .nilLit, getHint "Scalene" fields])

-- Parent replay starts with the actual incoming fields, including argument writes.
def withBody (body : Checker.Expr) : Checker.Expr := .seq [parentExpr,
  .class' "Triangle" (some (.const "Shape")) (.def' "initialize" [] body), getExpr]
def extraFields : Ty := .ivarCons "@tag" .int fields
#guard validateD (withBody (.seq [.vasgn .ivar "@tag" (.int 8), .super' [.int 3] none]))
  (.seq [parentHint, childHint (.seq [.ivarAsgn "@tag" (.intLit 8), .superInit [.intLit 3]]),
    getHint "Triangle" extraFields])
#guard validateD (withBody (.super' [.vasgn .ivar "@tag" (.int 3)] none))
  (.seq [parentHint, childHint (.superInit [.ivarAsgn "@tag" (.intLit 3)]), getHint "Triangle" extraFields])

def twoArgs : Checker.Expr := .seq [
  .class' "Shape" none (.seq [
    .def' "initialize" [.req "first", .req "last"] (.vasgn .ivar "@sides" (.var .lvar "last")),
    .def' "sides" [] (.var .ivar "@sides")]),
  .class' "Triangle" (some (.const "Shape")) (.def' "initialize" []
    (.super' [.vasgn .ivar "@tag" (.int 1), .vasgn .ivar "@tag" (.int 2)] none)), getExpr]
#guard validateD twoArgs (.seq [
  .classDecl "Shape" none (.seq [
    .defDecl "initialize" [("first", .int), ("last", .int)] .any (.ivarAsgn "@sides" (.var .lvar "last")),
    .defDecl "sides" [] .int (.ivarRead "@sides" .int)]),
  childHint (.superInit [.ivarAsgn "@tag" (.intLit 1), .ivarAsgn "@tag" (.intLit 2)]),
  getHint "Triangle" extraFields])
#guard match Interp.run 240 (evalFrom bootMachine twoArgs) with
  | .value (.int 2) _ => true
  | _ => false

-- No parent, explicit block, splat or implicit-argument forwarding is claimed.
#guard !validateD (.class' "Solo" none (.def' "initialize" [] (.super' [] none)))
  (.classDecl "Solo" none (.defDecl "initialize" [] .any (.superInit [])))
#guard !validateD (withBody (.super' [.int 3] (some (.int 9)))) (hint [.intLit 3])
#guard !validateD (withBody (.zsuper none)) (hint [])
#guard !validateD (programArgs [.splat (some (.array [.int 3]))]) (hint [.intLit 3])

end Checker.Soundness.Typed.SuperCheckControls
