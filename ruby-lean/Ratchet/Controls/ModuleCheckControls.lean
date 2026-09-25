import Ratchet.Check.Check

/-! Module certificates check bodies, preserve caller locals and grant no allocator.
Inferred signatures are ordinary untrusted defDecl hints, checked even when uncalled. -/
namespace Ratchet.ModuleCheckControls

def declaration (name : String) (body : Expr := .int 7) : Expr :=
  .module' name (.defs .self' "answer" [] body)
def hint (name : String) (ret : Ty := .int) (body : Deriv := .intLit 7) : Deriv :=
  .moduleDecl name (.defDecl "answer" [] ret body)
def call (name : String) : Expr := .send (some (.const name)) "answer" [] none
def callHint (name : String) (ret : Ty := .int) : Deriv :=
  .callSingleton (.constCls name) "answer" [] ret

#guard validateD (.seq [declaration "Answers", call "Answers"])
  (.seq [hint "Answers", callHint "Answers"])
#guard validateD (.seq [declaration "Renamed", call "Renamed"])
  (.seq [hint "Renamed", callHint "Renamed"])
#guard validateD (.seq [declaration "Answers", .module' "Later" .nil, call "Answers"])
  (.seq [hint "Answers", .moduleDecl "Later" .nilLit, callHint "Answers"])
#guard !validateD (declaration "Answers") (hint "Different")
#guard !validateD (declaration "Answers") (hint "Answers" (.cls "String"))
#guard !validateD (.seq [declaration "Answers", call "Answers"])
  (.seq [hint "Answers", callHint "Answers" (.cls "String")])
-- An uncalled forged body is rejected, as is an extra argument to the zero-arg body.
#guard !validateD (declaration "Answers" (.send (some (.int 7)) "+" [.tru] none))
  (hint "Answers" .int (.prim (.intLit 7) "+" [.truLit] .int .int))
#guard !validateD (.seq [declaration "Answers", .send (some (.const "Answers")) "answer" [.int 1] none])
  (.seq [hint "Answers", .callSingleton (.constCls "Answers") "answer" [.intLit 1] .int])
#guard !validateD (.seq [declaration "Answers", declaration "Answers"])
  (.seq [hint "Answers", hint "Answers"])
#guard !validateD (.seq [declaration "Answers", .send (some (.const "Answers")) "new" [] none])
  (.seq [hint "Answers", .newInst "Answers" [] (.inst "Answers" .ivar0)])
#guard !validateD (.seq [declaration "Answers", .class' "Child" (some (.const "Answers")) .nil])
  (.seq [hint "Answers", .classDecl "Child" (some "Answers") .nilLit])
-- Module expressions retain the actual body result; outer locals are not captured.
#guard (check fuelD [] (.module' "Value" (.int 7)) (.moduleDecl "Value" (.intLit 7))).map (·.ty) == some .int
#guard validateD (.seq [.vasgn .lvar "keep" (.int 3),
  .module' "Value" (.vasgn .lvar "keep" (.int 7)), .var .lvar "keep"])
  (.seq [.vasgn .lvar "keep" (.intLit 3),
    .moduleDecl "Value" (.vasgn .lvar "keep" (.intLit 7)), .var .lvar "keep"])
#guard !validateD (.seq [.vasgn .lvar "keep" (.int 3), .module' "Value" (.var .lvar "keep")])
  (.seq [.vasgn .lvar "keep" (.intLit 3), .moduleDecl "Value" (.var .lvar "keep")])
end Ratchet.ModuleCheckControls
