import Ratchet.Controls.ClassCheckControls

/-! Whole-program inheritance controls. Every source annotation is replayed for every
effective receiver before acceptance, including methods which are never called. -/
namespace Ratchet.InheritanceControls
open ClassCheckControls

def child (name parent : String) (body : Expr := .nil) : Expr :=
  .class' name (some (.const parent)) body
def childHint (name parent : String) (body : Deriv := .nilLit) : Deriv :=
  .classDecl name (some parent) body
def program (parent name : String) (arg : Expr) : Expr :=
  .seq [cls parent, child name parent, getExpr name arg]
def hint (parent name : String) (ty : Ty) (arg : Deriv) : Deriv :=
  .seq [clsHint parent ty, childHint name parent, getHint name ty arg]

#guard validateD (program "LabelBox" "LabelChild" (.str "Rex"))
  (hint "LabelBox" "LabelChild" (.cls "String") (.strLit "Rex"))
#guard (check fuelD [] (program "LabelBox" "LabelChild" (.str "Rex"))
  (hint "LabelBox" "LabelChild" (.cls "String") (.strLit "Rex"))).map (·.ty) == some (.cls "String")
#guard validateD (program "Switch" "Relay" .tru) (hint "Switch" "Relay" .bool .truLit)
#guard validateD (.seq [cls "Store", child "Branch" "Store", child "Leaf" "Branch",
  getExpr "Leaf" (.int 9)])
  (.seq [clsHint "Store" .int, childHint "Branch" "Store", childHint "Leaf" "Branch",
    getHint "Leaf" .int (.intLit 9)])

-- The subclass alone must reject an inherited body invalidated by its initializer.
def definitions : Expr := .seq [cls "LabelBox", child "LabelChild" "LabelBox" initDecl]
def definitionsHint (ty : Ty) : Deriv := .seq [clsHint "LabelBox" (.cls "String"),
  childHint "LabelChild" "LabelBox" (initHint ty)]
#guard validateD definitions (definitionsHint (.cls "String"))
#guard !validateD definitions (definitionsHint .int)
#guard !validateD definitions (definitionsHint (.nilable (.cls "String")))
#guard !validateD (.seq [definitions, getExpr "LabelChild" (.str "Rex")])
  (.seq [definitionsHint (.nilable (.cls "String")),
    getHint "LabelChild" (.cls "String") (.strLit "Rex")])
-- An invalid parent body cannot be hidden behind an empty child and no calls.
#guard !validateD (.seq [cls "LabelBox", child "LabelChild" "LabelBox"])
  (.seq [.classDecl "LabelBox" none
    (.seq [initHint (.nilable (.cls "String")), getterHint (.cls "String") (.cls "String")]),
    childHint "LabelChild" "LabelBox"])

-- An inherited argument annotation is not specialized to this valid-looking call.
#guard validateD (.seq [cls "Counter" [add], child "CounterChild" "Counter",
  .send (some (newExpr "CounterChild" (.int 10))) "add" [.int 5] none])
  (.seq [clsHint "Counter" .int [addHint], childHint "CounterChild" "Counter",
    .callMethodSig (newHint "CounterChild" .int (.intLit 10)) "add" [.intLit 5] .int])
#guard !validateD (.seq [cls "Counter" [add], child "CounterChild" "Counter"])
  (.seq [clsHint "Counter" .int [addHint (.nilable .int)], childHint "CounterChild" "Counter"])
#guard !validateD (.seq [cls "Counter" [add], child "CounterChild" "Counter",
  .send (some (newExpr "CounterChild" (.int 10))) "add" [.int 5] none])
  (.seq [clsHint "Counter" .int [addHint (.nilable .int)], childHint "CounterChild" "Counter",
    .callMethodSig (newHint "CounterChild" .int (.intLit 10)) "add" [.intLit 5] .int])
#guard !validateD (program "Store" "Branch" .tru) (hint "Store" "Branch" .int .truLit)
#guard !validateD (.seq [cls "Store", child "Branch" "Store",
  .send (some (.const "Branch")) "new" [] none])
  (.seq [clsHint "Store" .int, childHint "Branch" "Store",
    .newInst "Branch" [] (.inst "Branch" (fields .int))])
#guard !validateD (.seq [cls "Store", child "Branch" "Store", newExpr "Branch" (.int 1)])
  (.seq [clsHint "Store" .int, childHint "Branch" "Store",
    .newInst "Branch" [.intLit 1] (.inst "Branch" (fields .bool))])
#guard !validateD (child "Branch" "Missing") (childHint "Branch" "Missing")
#guard !validateD (child "Cycle" "Cycle") (childHint "Cycle" "Cycle")
#guard !validateD (.seq [cls "Store", child "Branch" "Store"])
  (.seq [clsHint "Store" .int, childHint "Branch" "Missing"])

-- First-owner lookup: a child override is checked and used, never the cached parent.
def override : Expr := .def' "get" [] .tru
def overrideHint (ret : Ty := .bool) : Deriv := .defDecl "get" [] ret .truLit
#guard validateD (.seq [cls "Store", child "Branch" "Store" override,
  getExpr "Branch" (.int 1)])
  (.seq [clsHint "Store" .int, childHint "Branch" "Store" overrideHint,
    .callMethodSig (newHint "Branch" .int (.intLit 1)) "get" [] .bool])
#guard !validateD (.seq [cls "Store", child "Branch" "Store" override])
  (.seq [clsHint "Store" .int, childHint "Branch" "Store" (overrideHint .int)])
#guard !validateD (.seq [cls "Store", child "Branch" "Store" override,
  getExpr "Branch" (.int 1)])
  (.seq [clsHint "Store" .int, childHint "Branch" "Store" overrideHint,
    getHint "Branch" .int (.intLit 1)])

-- Own native-named methods retain their old route; inherited native names are gated.
def native : Expr := .def' "length" [] (.var .ivar "@value")
def nativeHint : Deriv := .defDecl "length" [] .int (.ivarRead "@value" .int)
def nativeProgram (receiver : String) : Expr := .seq [cls "Store" [native], child "Branch" "Store",
  .send (some (newExpr receiver (.int 1))) "length" [] none]
def nativeProgramHint (receiver : String) : Deriv :=
  .seq [clsHint "Store" .int [nativeHint], childHint "Branch" "Store",
    .callMethodSig (newHint receiver .int (.intLit 1)) "length" [] .int]
#guard validateD (nativeProgram "Store") (nativeProgramHint "Store")
#guard !validateD (nativeProgram "Branch") (nativeProgramHint "Branch")

-- No initializer row does not mean a proved zero-argument allocator (frontier 066).
#guard !validateD (.seq [.class' "Base" none .nil, child "Child" "Base",
  .send (some (.const "Child")) "new" [] none])
  (.seq [.classDecl "Base" none .nilLit, childHint "Child" "Base",
    .newInst "Child" [] (.inst "Child" .ivar0)])

end Ratchet.InheritanceControls
