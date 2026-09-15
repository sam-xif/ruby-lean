import Ratchet.ClassCheckControls

/-! Definition-plus-call controls for annotation-checked method-to-method dispatch. -/
namespace Ratchet.MemberCallControls
open ClassCheckControls

def relay (name : String := "get") : Expr := .def' "relay" [] (.vcall name)
def relayHint (input ret : Ty) (name : String := "get") : Deriv :=
  .defDecl "relay" [] ret (.callSig name [] input)
def relayCall (name : String) (arg : Expr) : Expr :=
  .send (some (newExpr name arg)) "relay" [] none
def relayCallHint (name : String) (ty : Ty) (arg : Deriv) : Deriv :=
  .callMethodSig (newHint name ty arg) "relay" [] ty
def fullRelay (name : String) (arg : Expr) : Expr := .seq [cls name [relay], relayCall name arg]
def fullRelayHint (name : String) (ty : Ty) (arg : Deriv) : Deriv :=
  .seq [clsHint name ty [relayHint ty ty], relayCallHint name ty arg]

#guard validateD (cls "Packet" [relay]) (clsHint "Packet" .int [relayHint .int .int])
#guard validateD (fullRelay "Packet" (.int 4)) (fullRelayHint "Packet" .int (.intLit 4))
#guard validateD (fullRelay "Switch" .tru) (fullRelayHint "Switch" .bool .truLit)
#guard validateD (fullRelay "Values" (.array [.int 1]))
  (fullRelayHint "Values" (.arrayOf .int) (.arrayLit [.intLit 1] .int))
#guard validateD (fullRelay "OptionalBox" (.if' .tru (.int 1) (some .nil)))
  (fullRelayHint "OptionalBox" (.nilable .int) (.ifD .truLit (.intLit 1) (some .nilLit) (.nilable .int)))

-- Bad uncalled bodies are rejected at the declaration, before any call-site values exist.
#guard !validateD (cls "Switch" [relay]) (clsHint "Switch" .bool [relayHint .bool .int])
#guard !validateD (cls "Switch" [relay]) (clsHint "Switch" .bool [relayHint .int .int])
#guard !validateD (cls "OptionalBox" [relay])
  (clsHint "OptionalBox" (.nilable .int) [relayHint (.nilable .int) .int])
#guard !validateD (cls "Packet" [relay "missing"])
  (clsHint "Packet" .int [relayHint .int .int "missing"])
#guard !validateD (cls "Counter" [add, relay "add"])
  (clsHint "Counter" .int [addHint, relayHint .int .int "add"])
#guard !validateD (cls "Packet" [relay "initialize"])
  (clsHint "Packet" .int [relayHint .any .any "initialize"])
#guard !validateD (cls "Packet" [relay])
  (clsHint "Packet" .int [.defDecl "relay" [] .int (.callSig "get" [.intLit 1] .int)])
#guard !validateD (cls "Packet" [relay]) (clsHint "Packet" .int [relayHint .int .int "wrong"])

-- A successful bare call must still type its consuming expression, not just its leaf.
def incGet : Expr := .def' "incGet" [] (.send (some (.vcall "get")) "+" [.int 1] none)
def incGetHint (input : Ty := .int) : Deriv := .defDecl "incGet" [] .int
  (.prim (.callSig "get" [] input) "+" [.intLit 1] .int .int)
#guard validateD (cls "Counter" [incGet]) (clsHint "Counter" .int [incGetHint])
#guard !validateD (cls "Counter" [incGet]) (clsHint "Counter" .bool [incGetHint .bool])
#guard !validateD (cls "Counter" [incGet, relay "incGet", plusDef])
  (clsHint "Counter" .int [incGetHint, relayHint .int .int "incGet", plusHint])

-- Same selectors on two owners retain distinct return annotations after cache refresh.
#guard validateD (.seq [cls "Alpha" [relay], cls "Beta" [relay],
  relayCall "Alpha" (.int 9), relayCall "Beta" .fls])
  (.seq [clsHint "Alpha" .int [relayHint .int .int], clsHint "Beta" .bool [relayHint .bool .bool],
    relayCallHint "Alpha" .int (.intLit 9), relayCallHint "Beta" .bool .flsLit])

-- Cross-class dispatch restores the caller's Integer fields after the Boolean callee.
def cross : Expr := .def' "probe" [.req "other"] (.seq [
  .send (some (.var .lvar "other")) "get" [] none, .var .ivar "@value"])
def crossHint (domain : Ty := .inst "Beta" (fields .bool)) : Deriv :=
  .defDecl "probe" [("other", domain)] .int (.seq [
    .callMethodSig (.var .lvar "other") "get" [] .bool, .ivarRead "@value" .int])
def crossCall : Expr := .send (some (newExpr "Alpha" (.int 9))) "probe" [newExpr "Beta" .tru] none
def crossCallHint : Deriv := .callMethodSig (newHint "Alpha" .int (.intLit 9)) "probe"
  [newHint "Beta" .bool .truLit] .int
#guard validateD (.seq [cls "Beta", cls "Alpha" [cross], crossCall])
  (.seq [clsHint "Beta" .bool, clsHint "Alpha" .int [crossHint], crossCallHint])
#guard !validateD (.seq [cls "Beta", cls "Alpha" [cross]])
  (.seq [clsHint "Beta" .bool, clsHint "Alpha" .int [crossHint (.inst "Beta" (fields .int))]])

end Ratchet.MemberCallControls
