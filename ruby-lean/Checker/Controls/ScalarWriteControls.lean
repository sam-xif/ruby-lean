import Checker.Controls.ClassCheckControls

/-! Scalar writes retain an existing field domain; initializer writes remain a different
judgment. Aliases in locals and collections must keep their field claims after a call. -/
namespace Checker.ScalarWriteControls
open ClassCheckControls (initDecl initHint fields getter getterHint newExpr newHint getHint)

def setter (value : Expr) : Expr := .def' "set" [] (.vasgn .ivar "@value" value)
def setterHint (ty : Ty) (d : Deriv) : Deriv := .defDecl "set" [] ty (.ivarAsgn "@value" d)
def cls (cn : String) (value : Expr) : Expr := .class' cn none (.seq [initDecl, getter, setter value])
def hint (cn : String) (ty : Ty) (d : Deriv) : Deriv :=
  .classDecl cn none (.seq [initHint ty, getterHint ty ty, setterHint ty d])
def call (cn : String) (initial : Expr) : Expr := .send (some (newExpr cn initial)) "set" [] none
def callHint (cn : String) (ty : Ty) (d : Deriv) : Deriv :=
  .callMethodSig (newHint cn ty d) "set" [] ty

#guard validateD (.seq [cls "Counter" (.int 9), call "Counter" (.int 1)])
  (.seq [hint "Counter" .int (.intLit 9), callHint "Counter" .int (.intLit 1)])
#guard validateD (.seq [cls "Tag" (.sym "new"), call "Tag" (.sym "old")])
  (.seq [hint "Tag" .sym (.symLit "new"), callHint "Tag" .sym (.symLit "old")])
#guard validateD (cls "FloatBox" (.flt 0)) (hint "FloatBox" .float (.fltLit 0))
-- nil is refused like Boolean: a nil-typed field may be absent, so the receiver could be
-- frozen (`Guards/ScalarWrite.lean`).
#guard !validateD (cls "NilBox" .nil) (hint "NilBox" .nilT .nilLit)
#guard !validateD (cls "FlagBox" .fls) (hint "FlagBox" .bool .flsLit)
#guard !validateD (cls "Counter" (.str "bad"))
  (.classDecl "Counter" none (.seq [initHint .int, getterHint .int .int,
    setterHint (.cls "String") (.strLit "bad")]))
#guard !validateD (.class' "Counter" none (.seq [initDecl, .def' "set" [] (.vasgn .ivar "@other" (.int 9))]))
  (.classDecl "Counter" none (.seq [initHint .int, .defDecl "set" [] .int (.ivarAsgn "@other" (.intLit 9))]))
#guard !validateD (cls "Counter" (.int 9))
  (.classDecl "Counter" none (.seq [initHint .int, getterHint .int .int,
    .defDecl "set" [] .int (.ivarAsgn "@wrong" (.intLit 9))]))

-- Two aliases and an array retain the same initialized receiver through mutation.
def aliases : Expr := .seq [cls "Counter" (.int 9),
  .vasgn .lvar "a" (newExpr "Counter" (.int 1)),
  .vasgn .lvar "b" (.var .lvar "a"), .vasgn .lvar "xs" (.array [.var .lvar "a"]),
  .send (some (.var .lvar "a")) "set" [] none,
  .send (some (.var .lvar "b")) "get" [] none]
def aliasesHint : Deriv := .seq [hint "Counter" .int (.intLit 9),
  .vasgn .lvar "a" (newHint "Counter" .int (.intLit 1)),
  .vasgn .lvar "b" (.var .lvar "a"),
  .vasgn .lvar "xs" (.arrayLit [.var .lvar "a"] (.inst "Counter" (fields .int))),
  .callMethodSig (.var .lvar "a") "set" [] .int,
  .callMethodSig (.var .lvar "b") "get" [] .int]
#guard validateD aliases aliasesHint

-- A narrower call value cannot repair a method declared over a nullable domain.
#guard !validateD (.class' "Counter" none (.seq [initDecl,
  .def' "set" [.req "n"] (.vasgn .ivar "@value" (.var .lvar "n"))]))
  (.classDecl "Counter" none (.seq [initHint .int,
    .defDecl "set" [("n", .nilable .int)] (.nilable .int) (.ivarAsgn "@value" (.var .lvar "n"))]))
end Checker.ScalarWriteControls
