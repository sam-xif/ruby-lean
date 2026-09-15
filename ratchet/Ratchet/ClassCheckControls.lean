import Ratchet.Check

/-! Whole-class positives and adversarial annotation/cache controls. Names, parameter types
and field types vary; acceptance includes the body, not merely its signature or definition. -/
namespace Ratchet.ClassCheckControls

def fields (ty : Ty) : Ty := .ivarCons "@value" ty .ivar0
def initBody : Expr := .vasgn .ivar "@value" (.var .lvar "value")
def initDecl : Expr := .def' "initialize" [.req "value"] initBody
def initHint (input : Ty) (ret : Ty := .any) : Deriv :=
  .defDecl "initialize" [("value", input)] ret (.ivarAsgn "@value" (.var .lvar "value"))
def getter : Expr := .def' "get" [] (.var .ivar "@value")
def getterHint (input ret : Ty) : Deriv := .defDecl "get" [] ret (.ivarRead "@value" input)
def cls (name : String) (extra : List Expr := []) : Expr :=
  .class' name none (.seq ([initDecl, getter] ++ extra))
def clsHint (name : String) (input : Ty) (extra : List Deriv := []) : Deriv :=
  .classDecl name none (.seq ([initHint input, getterHint input input] ++ extra))
def newExpr (name : String) (arg : Expr) : Expr := .send (some (.const name)) "new" [arg] none
def newHint (name : String) (input : Ty) (arg : Deriv) : Deriv := .newInst name [arg] (.inst name (fields input))
def getExpr (name : String) (arg : Expr) : Expr := .send (some (newExpr name arg)) "get" [] none
def getHint (name : String) (input : Ty) (arg : Deriv) : Deriv :=
  .callMethodSig (newHint name input arg) "get" [] input
def full (name : String) (arg : Expr) : Expr := .seq [cls name, getExpr name arg]
def fullHint (name : String) (input : Ty) (arg : Deriv) : Deriv :=
  .seq [clsHint name input, getHint name input arg]

#guard validateD (cls "Packet") (clsHint "Packet" .int)
#guard validateD (full "Packet" (.int 7)) (fullHint "Packet" .int (.intLit 7))
#guard (check fuelD [] (full "Packet" (.int 7)) (fullHint "Packet" .int (.intLit 7))).map (·.ty) == some .int
#guard validateD (full "Switch" .fls) (fullHint "Switch" .bool .flsLit)
#guard validateD (.seq [.class' "FlagBox" none (.def' "initialize" [.req "flag"] (.var .lvar "flag")),
  newExpr "FlagBox" .tru])
  (.seq [.classDecl "FlagBox" none (.defDecl "initialize" [("flag", .bool)] .bool (.var .lvar "flag")),
    .newInst "FlagBox" [.truLit] (.inst "FlagBox" .ivar0)])
#guard !validateD (.seq [.class' "FlagBox" none (.def' "initialize" [.req "flag"] (.var .lvar "flag")),
  newExpr "FlagBox" .tru])
  (.seq [.classDecl "FlagBox" none (.defDecl "initialize" [("flag", .bool)] .bool (.var .lvar "flag")),
    .newInst "FlagBox" [.truLit] .bool])
#guard validateD (full "Values" (.array [.int 1]))
  (fullHint "Values" (.arrayOf .int) (.arrayLit [.intLit 1] .int))
#guard validateD (full "OptionalBox" (.if' .tru (.int 1) (some .nil)))
  (fullHint "OptionalBox" (.nilable .int) (.ifD .truLit (.intLit 1) (some .nilLit) (.nilable .int)))

-- Bad return annotations are rejected before any constructor or method call is present.
#guard !validateD (cls "Packet")
  (.classDecl "Packet" none (.seq [initHint .int .bool, getterHint .int .int]))
#guard !validateD (cls "Packet")
  (.classDecl "Packet" none (.seq [initHint .int, getterHint .int .bool]))
-- A nullable initializer domain cannot be narrowed to Integer by the getter or its hint.
#guard !validateD (cls "Packet")
  (.classDecl "Packet" none (.seq [initHint (.nilable .int), getterHint (.nilable .int) .int]))
#guard !validateD (cls "Packet")
  (.classDecl "Packet" none (.seq [initHint (.nilable .int), getterHint .int .int]))

def add : Expr := .def' "add" [.req "k"] (.send (some (.var .ivar "@value")) "+" [.var .lvar "k"] none)
def addHint (input : Ty := .int) : Deriv := .defDecl "add" [("k", input)] .int
  (.prim (.ivarRead "@value" .int) "+" [.var .lvar "k"] .int .int)
def addCall : Expr := .send (some (newExpr "Counter" (.int 10))) "add" [.int 5] none
def addCallHint : Deriv := .callMethodSig (newHint "Counter" .int (.intLit 10)) "add" [.intLit 5] .int
#guard validateD (cls "Counter" [add]) (clsHint "Counter" .int [addHint])
#guard validateD (.seq [cls "Counter" [add], addCall]) (.seq [clsHint "Counter" .int [addHint], addCallHint])
#guard !validateD (cls "Counter" [add]) (clsHint "Counter" .int [addHint (.nilable .int)])
#guard !validateD (.seq [cls "Counter" [add], addCall])
  (.seq [clsHint "Counter" .int [addHint (.nilable .int)], addCallHint])

-- Ignore-result is not ignore-body; no missing suffix, bad local, or unknown send passes.
def badInit : Expr := .class' "Broken" none (.def' "initialize" [.req "value"]
  (.seq [initBody, .send none "missing" [] none]))
#guard !validateD badInit (.classDecl "Broken" none
  (.defDecl "initialize" [("value", .int)] .any
    (.seq [.ivarAsgn "@value" (.var .lvar "value"), .callSig "missing" [] .any])))
#guard !validateD badInit (.classDecl "Broken" none (initHint .int))
#guard !validateD (cls "Counter" [.def' "unused" [] (.var .lvar "caller")])
  (clsHint "Counter" .int [.defDecl "unused" [] .int (.var .lvar "caller")])

-- Wrong arguments/arity/claimed field shape, wrong names, unsupported default allocator.
#guard !validateD (full "Packet" .tru) (fullHint "Packet" .int .truLit)
#guard !validateD (.seq [cls "Packet", .send (some (.const "Packet")) "new" [] none])
  (.seq [clsHint "Packet" .int, .newInst "Packet" [] (.inst "Packet" (fields .int))])
#guard !validateD (.seq [cls "Packet", newExpr "Packet" (.int 1)])
  (.seq [clsHint "Packet" .int, .newInst "Packet" [.intLit 1] (.inst "Packet" (fields .bool))])
#guard !validateD (cls "Packet") (clsHint "Other" .int)
#guard !validateD (.seq [.class' "EmptyBox" none (.int 1), .send (some (.const "EmptyBox")) "new" [] none])
  (.seq [.classDecl "EmptyBox" none (.intLit 1), .newInst "EmptyBox" [] (.inst "EmptyBox" .ivar0)])
#guard (check 0 [] (cls "Packet") (clsHint "Packet" .int)).isNone

-- Updating a table invalidates cached primitive guards, even for uncalled methods.
def plusDef : Expr := .def' "+" [.req "other"] (.var .lvar "other")
def plusHint : Deriv := .defDecl "+" [("other", .int)] .int (.var .lvar "other")
#guard !validateD (cls "Counter" [add, plusDef]) (clsHint "Counter" .int [addHint, plusHint])
def topInc : Expr := .def' "inc" [.req "x"] (.send (some (.var .lvar "x")) "+" [.int 1] none)
def topHint : Deriv := .defDecl "inc" [("x", .int)] .int
  (.prim (.var .lvar "x") "+" [.intLit 1] .int .int)
#guard validateD (.seq [topInc, cls "Counter"]) (.seq [topHint, clsHint "Counter" .int])
#guard !validateD (.seq [topInc, cls "Counter" [plusDef]]) (.seq [topHint, clsHint "Counter" .int [plusHint]])

-- Same method names on different classes retain independent annotation/body caches.
#guard validateD (.seq [cls "AlphaBox", cls "BetaBox", getExpr "AlphaBox" (.int 1), getExpr "BetaBox" .tru])
  (.seq [clsHint "AlphaBox" .int, clsHint "BetaBox" .bool,
    getHint "AlphaBox" .int (.intLit 1), getHint "BetaBox" .bool .truLit])
#guard !validateD (.seq [cls "AlphaBox", cls "BetaBox", getExpr "AlphaBox" .tru])
  (.seq [clsHint "AlphaBox" .int, clsHint "BetaBox" .bool, getHint "AlphaBox" .bool .truLit])
#guard !validateD (.seq [cls "Packet", cls "Packet"])
  (.seq [clsHint "Packet" .int, clsHint "Packet" .int])

-- Refresh never lets a replay hint replace the stored parameter or return annotation.
private def checked := check fuelD [] (cls "Packet") (clsHint "Packet" .int)
#guard checked.any fun c => (refreshBodies fuelD c.ctx .ivar0 c.cache).isSome
#guard checked.any fun c => (refreshBodies fuelD c.ctx .ivar0 { c.cache with
  members := c.cache.members.map fun b => { b with deriv := .truLit } }).isNone
#guard checked.any fun c => (refreshBodies fuelD c.ctx .ivar0 { c.cache with
  initializers := c.cache.initializers.map fun b => { b with deriv := .truLit } }).isNone
#guard checked.any fun c => (findMember ctx0 (classHeader "Packet") "get" c.cache.members).isNone
#guard checked.any fun c => (findInitializer ctx0 (classHeader "Packet") c.cache.initializers).isNone

-- The same source code in both branches still needs compatible declared signatures.
#guard validateD (.if' .tru (cls "Packet") (some (cls "Packet")))
  (.ifD .truLit (clsHint "Packet" .int) (some (clsHint "Packet" .int)) .sym)
#guard !validateD (.if' .tru (cls "Packet") (some (cls "Packet")))
  (.ifD .truLit (clsHint "Packet" .int) (some (clsHint "Packet" .bool)) .sym)

end Ratchet.ClassCheckControls
