import Books.TypeSoundness.Checker.Controls.SingletonCheckControls

/-! Retain a body's proved result while still checking its declared annotation. Calls may
request either proof, but cannot invent fields or specialize a declared parameter domain. -/
namespace Checker.ResultControls
open ClassCheckControls

def identity (body : Expr := .self') : Expr := .def' "myself" [] body
def identityHint (cn : String) (ret : Ty := .cls cn) (body : Deriv := .selfExpr) : Deriv :=
  .defDecl "myself" [] ret body
def klass (cn : String) (body : Expr := .self') : Expr := cls cn [identity body]
def klassHint (cn : String) (ty : Ty := .int) (ret : Ty := .cls cn) (body : Deriv := .selfExpr) : Deriv :=
  clsHint cn ty [identityHint cn ret body]
def call (cn : String) (arg : Expr) : Expr := .send (some (newExpr cn arg)) "myself" [] none
def callHint (cn : String) (ty : Ty) (arg : Deriv) (ret : Ty) : Deriv :=
  .callMethodSig (newHint cn ty arg) "myself" [] ret
def program (cn : String) (arg : Expr) (body : Expr := .self') : Expr :=
  .seq [klass cn body, .send (some (call cn arg)) "get" [] none]
def hint (cn : String) (ty : Ty) (arg : Deriv) (body : Deriv := .selfExpr) : Deriv :=
  .seq [klassHint cn ty (.cls cn) body,
    .callMethodSig (callHint cn ty arg (.inst cn (fields ty))) "get" [] ty]

#guard validateD (program "Coordinate" (.int 7)) (hint "Coordinate" .int (.intLit 7))
#guard validateD (program "Flag" .tru) (hint "Flag" .bool .truLit)
#guard validateD (program "Coordinate" (.int 7) (.seq [.vasgn .lvar "saved" .self', .var .lvar "saved"]))
  (hint "Coordinate" .int (.intLit 7) (.seq [.vasgn .lvar "saved" .selfExpr, .var .lvar "saved"]))
#guard validateD (.seq [klass "Coordinate", call "Coordinate" (.int 7)])
  (.seq [klassHint "Coordinate", callHint "Coordinate" .int (.intLit 7) (.cls "Coordinate")])
#guard !validateD (klass "Coordinate") (klassHint "Coordinate" .int .int)
#guard !validateD (klass "Coordinate" .fls) (klassHint "Coordinate" .int (.cls "Coordinate") .flsLit)
#guard !validateD (.seq [klass "Coordinate", call "Coordinate" (.int 7)])
  (.seq [klassHint "Coordinate", callHint "Coordinate" .int (.intLit 7) (.inst "Coordinate" (fields .bool))])
#guard !validateD .self' .selfExpr

-- An opaque nominal parameter never supplies an initialized-instance result proof.
def relay : Defn := ⟨"relay", [.req "p"], .var .lvar "p"⟩
def relayBody := checkMethodBody 100 (topBodyCtx ctx0 relay) .ivar0 relay
  (.defDecl "relay" [("p", .cls "Coordinate")] (.cls "Coordinate") (.var .lvar "p"))
#guard relayBody.isSome
#guard relayBody.all fun b => (b.resultAt (.inst "Coordinate" (fields .int))).isNone
#guard relayBody.all fun b => (b.resultAt (.cls "Coordinate")).isSome

-- A top-level body can retain a parameter's proved field domain across its return.
#guard validateD (.seq [cls "Coordinate", .def' "relay" [.req "p"] (.var .lvar "p"),
  .send (some (.send none "relay" [newExpr "Coordinate" (.int 7)] none)) "get" [] none])
  (.seq [clsHint "Coordinate" .int,
    .defDecl "relay" [("p", .inst "Coordinate" (fields .int))] (.cls "Coordinate") (.var .lvar "p"),
    .callMethodSig (.callSig "relay" [newHint "Coordinate" .int (.intLit 7)]
      (.inst "Coordinate" (fields .int))) "get" [] .int])

-- Implicit own-instance calls consume the same retained body proof.
#guard validateD (.seq [cls "Coordinate" [identity, .def' "again" [] (.vcall "myself")],
  .send (some (.send (some (newExpr "Coordinate" (.int 7))) "again" [] none)) "get" [] none])
  (.seq [clsHint "Coordinate" .int [identityHint "Coordinate",
    .defDecl "again" [] (.cls "Coordinate") (.callSig "myself" [] (.inst "Coordinate" (fields .int)))],
    .callMethodSig (.callMethodSig (newHint "Coordinate" .int (.intLit 7)) "again" []
      (.inst "Coordinate" (fields .int))) "get" [] .int])

-- The same selection works for a singleton factory without changing its annotation.
#guard validateD (SingletonCheckControls.full "Parcel")
  (.seq [SingletonCheckControls.hint "Parcel",
    .callSingleton (.constCls "Parcel") "make" [.intLit 7] (.inst "Parcel" (fields .int))])
end Checker.ResultControls
