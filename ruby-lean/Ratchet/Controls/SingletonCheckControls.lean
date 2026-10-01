import Ratchet.Controls.ClassCheckControls

/-! Own singleton admission checks annotations, code identity, caller/owner scope and cache
refresh. The positive factory exercises definition, implicit new, nominal return and call. -/
namespace Ratchet.SingletonCheckControls
open ClassCheckControls (initDecl initHint fields getter getterHint plusDef plusHint)

def factory (body : Expr := .send none "new" [.var .lvar "value"] none) : Expr :=
  .defs .self' "make" [.req "value"] body
def factoryHint (cn : String) (input : Ty := .int) (ret : Ty := .cls cn)
    (db : Deriv := .newImplicit cn [.var .lvar "value"] (.inst cn (fields .int))) : Deriv :=
  .defDecl "make" [("value", input)] ret db
def cls (cn : String) (body : Expr := factory) : Expr :=
  .class' cn none (.seq [initDecl, body])
def hint (cn : String) (db : Deriv := factoryHint cn) : Deriv :=
  .classDecl cn none (.seq [initHint .int, db])
def call (cn : String) (args : List Expr := [.int 7]) : Expr :=
  .send (some (.const cn)) "make" args none
def callHint (cn : String) (args : List Deriv := [.intLit 7]) : Deriv :=
  .callSingleton (.constCls cn) "make" args (.cls cn)
def full (cn : String) : Expr := .seq [cls cn, call cn]
def fullHint (cn : String) : Deriv := .seq [hint cn, callHint cn]

#guard validateD (cls "Parcel") (hint "Parcel")
#guard validateD (full "Parcel") (fullHint "Parcel")
#guard (check fuelD [] (full "Parcel") (fullHint "Parcel")).map (·.ty) == some (.cls "Parcel")
#guard validateD (full "Package") (fullHint "Package")
-- The full declared domain is checked even if this invocation supplies an Integer.
#guard !validateD (full "Parcel")
  (.seq [hint "Parcel" (factoryHint "Parcel" (.nilable .int)), callHint "Parcel"])
#guard !validateD (cls "Parcel" (factory (.str "wrong")))
  (hint "Parcel" (factoryHint "Parcel" .int (.cls "Parcel") (.strLit "wrong")))
#guard !validateD (cls "Parcel") (hint "Parcel" (factoryHint "Parcel" .int (.cls "Other")))
#guard !validateD (cls "Parcel" (factory (.send none "new" [.tru] none)))
  (hint "Parcel" (factoryHint "Parcel" .int (.cls "Parcel")
    (.newImplicit "Parcel" [.truLit] (.inst "Parcel" (fields .int)))))
#guard !validateD (cls "Parcel" (factory (.send none "new" [] none)))
  (hint "Parcel" (factoryHint "Parcel" .int (.cls "Parcel")
    (.newImplicit "Parcel" [] (.inst "Parcel" (fields .int)))))
#guard !validateD (.seq [cls "Parcel", call "Parcel" []])
  (.seq [hint "Parcel", callHint "Parcel" []])
#guard !validateD (.seq [cls "Parcel", call "Parcel" [.tru]])
  (.seq [hint "Parcel", callHint "Parcel" [.truLit]])
#guard !validateD (full "Parcel")
  (.seq [hint "Parcel", .callSingleton (.constCls "Parcel") "make" [.intLit 7] .int])
-- A forged receiver name or field shape cannot turn a body hint into an allocator proof.
#guard !validateD (cls "Parcel") (hint "Parcel" (factoryHint "Other"))
#guard !validateD (cls "Parcel") (hint "Parcel" (factoryHint "Parcel" .int (.cls "Parcel")
  (.newImplicit "Parcel" [.var .lvar "value"] (.inst "Parcel" (fields .bool)))))
-- Ordinary methods and singletons of the same selector keep their own body artifacts.
def sameName : Expr := .class' "Parcel" none (.seq [initDecl, getter,
  .defs .self' "get" [] (.int 9)])
def sameHint : Deriv := .classDecl "Parcel" none (.seq [initHint .int, getterHint .int .int,
  .defDecl "get" [] .int (.intLit 9)])
#guard validateD (.seq [sameName, .send (some (.const "Parcel")) "get" [] none])
  (.seq [sameHint, .callSingleton (.constCls "Parcel") "get" [] .int])
-- Recheck old singleton bodies after later declarations invalidate primitive absence.
def increment : Expr := .defs .self' "increment" [.req "n"]
  (.send (some (.var .lvar "n")) "+" [.int 1] none)
def incrementHint : Deriv := .defDecl "increment" [("n", .int)] .int
  (.prim (.var .lvar "n") "+" [.intLit 1] .int .int)
#guard validateD (.class' "Counter" none increment) (.classDecl "Counter" none incrementHint)
#guard !validateD (.class' "Counter" none (.seq [increment, plusDef]))
  (.classDecl "Counter" none (.seq [incrementHint, plusHint]))
private def checked := check fuelD [] (cls "Parcel") (hint "Parcel")
#guard checked.any fun c => (refreshBodies fuelD c.ctx .ivar0 c.cache).isSome
#guard checked.any fun c => (refreshBodies fuelD c.ctx .ivar0 { c.cache with
  singletons := c.cache.singletons.map fun b => { b with deriv := .truLit } }).isNone
#guard checked.any fun c => (findSingleton ctx0 (classHeader "Parcel") "make" c.cache.singletons).isNone
#guard checked.any fun c => !singletonCacheCompleteB c.ctx { c.cache with singletons := [] }
-- Equal source bodies in both branches still require equal singleton annotations.
#guard !validateD (.if' .tru (.class' "Copy" none (.defs .self' "copy" [.req "x"] (.var .lvar "x")))
  (some (.class' "Copy" none (.defs .self' "copy" [.req "x"] (.var .lvar "x")))))
  (.ifD .truLit (.classDecl "Copy" none (.defDecl "copy" [("x", .int)] .int (.var .lvar "x")))
    (some (.classDecl "Copy" none (.defDecl "copy" [("x", .bool)] .bool (.var .lvar "x")))) .sym)
end Ratchet.SingletonCheckControls
