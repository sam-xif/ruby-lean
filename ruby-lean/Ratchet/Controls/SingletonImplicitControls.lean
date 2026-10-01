import Ratchet.Check.Check

/-! Implicit singleton dispatch checks self, arity, full domains and the own method
table. The same certificate shape supports bare calls and parenthesized sends. -/
namespace Ratchet.SingletonImplicitControls

def value : Expr := .defs .self' "value" [] (.int 21)
def valueHint : Deriv := .defDecl "value" [] .int (.intLit 21)
def describe (call : Expr := .vcall "value") : Expr :=
  .defs .self' "describe" [] (.send (some call) "*" [.int 2] none)
def describeHint (call : Deriv := .callSig "value" [] .int) : Deriv :=
  .defDecl "describe" [] .int (.prim call "*" [.intLit 2] .int .int)
def program (name : String) (call : Expr := .vcall "value") : Expr := .seq [
  .module' name (.seq [value, describe call]), .send (some (.const name)) "describe" [] none]
def hint (name : String) (call : Deriv := .callSig "value" [] .int) : Deriv := .seq [
  .moduleDecl name (.seq [valueHint, describeHint call]),
  .callSingleton (.constCls name) "describe" [] .int]

#guard validateD (program "Measured") (hint "Measured")
#guard validateD (program "Renamed" (.send none "value" [] none)) (hint "Renamed")
#guard !validateD (program "Measured") (hint "Measured" (.callSig "value" [] (.cls "String")))
#guard !validateD (program "Measured") (hint "Measured" (.callSig "value" [.intLit 2] .int))
#guard !validateD (program "Measured" (.send none "value" [.int 2] none))
  (hint "Measured" (.callSig "value" [.intLit 2] .int))
#guard !validateD (program "Measured" (.var .lvar "value")) (hint "Measured")

def increment : Expr := .defs .self' "increment" [.req "x"]
  (.send (some (.var .lvar "x")) "+" [.int 1] none)
def incrementHint (input : Ty := .int) : Deriv := .defDecl "increment" [("x", input)] .int
  (.prim (.var .lvar "x") "+" [.intLit 1] .int .int)
def relay (args : List Expr := [.int 7]) : Expr := .defs .self' "relay" []
  (.send none "increment" args none)
def relayHint (args : List Deriv := [.intLit 7]) : Deriv := .defDecl "relay" [] .int
  (.callSig "increment" args .int)
def withArg (body : Expr := relay) : Expr := .seq [
  .module' "Counter" (.seq [increment, body]), .send (some (.const "Counter")) "relay" [] none]
def withArgHint (input : Ty := .int) (body : Deriv := relayHint) : Deriv := .seq [
  .moduleDecl "Counter" (.seq [incrementHint input, body]),
  .callSingleton (.constCls "Counter") "relay" [] .int]
#guard validateD withArg withArgHint
#guard !validateD withArg (withArgHint (.nilable .int))
#guard !validateD (withArg (relay [.tru])) (withArgHint .int (relayHint [.truLit]))
#guard !validateD (withArg (.defs .self' "relay" [] (.vcall "increment")))
  (withArgHint .int (relayHint []))
-- No implicit access to another receiver's singleton or an instance-only method.
#guard !validateD (.seq [.module' "Provider" value, .module' "Consumer" (describe)])
  (.seq [.moduleDecl "Provider" valueHint, .moduleDecl "Consumer" describeHint])
#guard !validateD (.class' "InstanceOnly" none (.seq [
  .def' "value" [] (.int 21), describe]))
  (.classDecl "InstanceOnly" none (.seq [valueHint, describeHint]))
-- Identical instance/singleton selectors still select the singleton body.
#guard validateD (.seq [.class' "Both" none (.seq [
  .def' "value" [] (.str "wrong"), value, describe]),
  .send (some (.const "Both")) "describe" [] none])
  (.seq [.classDecl "Both" none (.seq [
    .defDecl "value" [] (.cls "String") (.strLit "wrong"), valueHint, describeHint]),
    .callSingleton (.constCls "Both") "describe" [] .int])
end Ratchet.SingletonImplicitControls
