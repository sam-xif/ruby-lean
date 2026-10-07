import Checker.Check.Check

/-! Attached blocks check source code, receiver-derived parameter types, physical
capture ownership and the loop's caller-type fixed point. No hint supplies those facts. -/
namespace Checker.MapCheckControls

private def plusX : Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def plusHint : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
private def arrayHint : Deriv := .arrayLit [.intLit 1] .int
private def map (body : Expr := plusX) (recv : Expr := .array [.int 1])
    (params : List Param := [.req "x"]) (locals : List String := []) : Expr :=
  .send (some recv) "map" [] (some (.block params locals body))
private def hint (body : Deriv := plusHint) (recv : Deriv := arrayHint) : Deriv :=
  .flow (.mapBlock recv body)

#guard validateD map hint
#guard validateD (map (.str "result")) (hint (.strLit "result"))
#guard ((check 100 [] (map (.str "result")) (hint (.strLit "result"))).map (·.ty)) == some (.arrayOf (.cls "String"))
#guard validateD (map (.int 7) (.array [])) (hint (.intLit 7) (.arrayLit [] .never))
#guard !validateD map (hint (.intLit 1))
#guard !validateD map (hint plusHint (.arrayLit [.intLit 2] .int))
#guard !validateD map (hint plusHint (.arrayLit [.intLit 1] (.cls "String")))
#guard !validateD (map plusX (.int 1)) (hint plusHint (.intLit 1))
#guard !validateD (map plusX (.array [.str "bad"])) (hint plusHint (.arrayLit [.strLit "bad"] (.cls "String")))
#guard !validateD (map plusX (.array [.int 1]) []) hint
#guard !validateD (map plusX (.array [.int 1]) [.req "x", .req "y"]) hint
#guard !validateD (map plusX (.array [.int 1]) [.rest (some "x")]) hint
#guard !validateD (.send (some (.array [.int 1])) "map" [.int 2] (some (.block [.req "x"] [] plusX))) hint
#guard !validateD (.send (some (.array [.int 1])) "each" [] (some (.block [.req "x"] [] plusX))) hint
#guard !validateD (.send (some (.array [.int 1])) "map" [] none) hint
#guard !validateD (map (.nxt (some (.int 1)))) (hint (.intLit 1))
#guard (check 100 [] map hint { ctx0 with neg := { ctx0.neg with declared := ["map"] } }).isNone

-- A hidden nil caller slot cannot receive the Integer parameter's type.
#guard validateD (.seq [.vasgn .lvar "x" .nil, map, .var .lvar "x"])
  (.flow (.seq [.vasgn .lvar "x" .nilLit, .mapBlock arrayHint plusHint, .var .lvar "x"]))
#guard !validateD (.seq [.vasgn .lvar "x" .nil, map, plusX])
  (.flow (.seq [.vasgn .lvar "x" .nilLit, .mapBlock arrayHint plusHint, plusHint]))

-- Stable writes to a live capture are admitted; changing its type is rejected.
#guard validateD (.seq [.vasgn .lvar "y" (.int 0), map (.vasgn .lvar "y" (.int 7))])
  (.flow (.seq [.vasgn .lvar "y" (.intLit 0), .mapBlock arrayHint (.vasgn .lvar "y" (.intLit 7))]))
#guard !validateD (.seq [.vasgn .lvar "y" (.int 0), map (.vasgn .lvar "y" .nil)])
  (.flow (.seq [.vasgn .lvar "y" (.intLit 0), .mapBlock arrayHint (.vasgn .lvar "y" .nilLit)]))

-- Parameter/block-local shadowing is distinct from a write to a capture.
#guard validateD (.seq [.vasgn .lvar "y" (.int 0), map (.vasgn .lvar "y" .nil) (.array [.int 1]) [.req "x"] ["y"]])
  (.flow (.seq [.vasgn .lvar "y" (.intLit 0), .mapBlock arrayHint (.vasgn .lvar "y" .nilLit)]))
#guard validateD (.send (some (.array [.int 1])) "collect" [] (some (.block [.req "x"] [] plusX))) hint
#guard (check 100 [] (.send (some (.array [.int 1])) "collect" []
  (some (.block [.req "x"] [] plusX))) hint
  { ctx0 with neg := { ctx0.neg with declared := ["collect"] } }).isNone
#guard !validateD (map (.send none "lambda" [] (some (.block [] [] (.int 1)))))
  (hint (.flow .closureLiteral))
end Checker.MapCheckControls
