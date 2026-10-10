import Books.TypeSoundness.Checker.Controls.ClassCheckControls

/-! Definitions after classes retain annotation-domain checking and refresh every cached
body. A caller cannot supply field facts that the declared parameter does not carry. -/
namespace Checker.TopClassControls
open ClassCheckControls

def reader (name : String := "read") : Expr :=
  .def' name [.req "p"] (.send (some (.var .lvar "p")) "get" [] none)
def readerHint (cn : String) (ty : Ty) (name : String := "read") : Deriv :=
  .defDecl name [("p", .inst cn (fields ty))] ty
    (.callMethodSig (.var .lvar "p") "get" [] ty)
def program (cn : String) (arg : Expr) (name : String := "read") : Expr :=
  .seq [cls cn, reader name, .send none name [newExpr cn arg] none]
def hint (cn : String) (ty : Ty) (arg : Deriv) (name : String := "read") : Deriv :=
  .seq [clsHint cn ty, readerHint cn ty name,
    .callSig name [newHint cn ty arg] ty]

#guard validateD (program "Coordinate" (.int 5)) (hint "Coordinate" .int (.intLit 5))
#guard validateD (program "Flag" .tru) (hint "Flag" .bool .truLit)
-- Equal selectors at Object and an instance owner do not overwrite each other's code.
#guard validateD (program "Coordinate" (.int 5) "get") (hint "Coordinate" .int (.intLit 5) "get")
#guard !validateD (program "Coordinate" .tru) (hint "Coordinate" .int .truLit)
#guard !validateD (.seq [cls "Coordinate", reader])
  (.seq [clsHint "Coordinate" .int, .defDecl "read" [("p", .inst "Coordinate" (fields .int))]
    .bool (.callMethodSig (.var .lvar "p") "get" [] .int)])
#guard !validateD (program "Coordinate" (.int 5))
  (.seq [clsHint "Coordinate" .int,
    .defDecl "read" [("p", .nilable (.inst "Coordinate" (fields .int)))] .int
      (.callMethodSig (.var .lvar "p") "get" [] .int),
    .callSig "read" [newHint "Coordinate" .int (.intLit 5)] .int])
#guard !validateD (.seq [cls "Coordinate", reader])
  (.seq [clsHint "Coordinate" .int, .defDecl "read" [("p", .cls "Coordinate")]
    .int (.callMethodSig (.var .lvar "p") "get" [] .int)])
#guard !validateD (.seq [cls "Coordinate", reader])
  (.seq [clsHint "Coordinate" .int, .defDecl "read" [("p", .inst "Coordinate" .ivar0)]
    .int (.callMethodSig (.var .lvar "p") "get" [] .int)])
-- The later definition invalidates an existing primitive absence guard, even uncalled.
#guard !validateD (.seq [cls "Counter" [add], plusDef])
  (.seq [clsHint "Counter" .int [addHint], plusHint])
#guard topDeclClassesB ctx0 "new"
#guard !topDeclClassesB { ctx0 with pos.classes := [classHeader "Point"] } "new"
#guard !topDeclClassesB { ctx0 with pos.classes := [classHeader "Object"] } "read"
end Checker.TopClassControls
