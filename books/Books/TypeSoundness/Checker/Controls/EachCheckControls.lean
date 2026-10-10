import Books.TypeSoundness.Checker.Check.Check

/-! Attached blocks check source code, receiver-derived parameter types, physical
capture ownership and the loop's caller-type fixed point. No hint supplies those facts. -/
namespace Checker.EachCheckControls

private def plusX : Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def plusHint : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
private def arrayHint : Deriv := .arrayLit [.intLit 1] .int
private def each (body : Expr := plusX) (recv : Expr := .array [.int 1])
    (params : List Param := [.req "x"]) (locals : List String := []) : Expr :=
  .send (some recv) "each" [] (some (.block params locals body))
private def hint (body : Deriv := plusHint) (recv : Deriv := arrayHint) : Deriv :=
  .flow (.eachBlock recv body)

#guard validateD each hint
#guard validateD (each (.str "ignored")) (hint (.strLit "ignored"))
#guard ((check 100 [] (each (.str "ignored")) (hint (.strLit "ignored"))).map (·.ty)) == some (.arrayOf .int)
#guard validateD (each (.int 7) (.array [])) (hint (.intLit 7) (.arrayLit [] .never))
#guard !validateD each (hint (.intLit 1))
#guard !validateD each (hint plusHint (.arrayLit [.intLit 2] .int))
#guard !validateD each (hint plusHint (.arrayLit [.intLit 1] (.cls "String")))
#guard !validateD (each plusX (.int 1)) (hint plusHint (.intLit 1))
#guard !validateD (each plusX (.array [.str "bad"])) (hint plusHint (.arrayLit [.strLit "bad"] (.cls "String")))
#guard !validateD (each plusX (.array [.int 1]) []) hint
#guard !validateD (each plusX (.array [.int 1]) [.req "x", .req "y"]) hint
#guard !validateD (each plusX (.array [.int 1]) [.rest (some "x")]) hint
#guard !validateD (.send (some (.array [.int 1])) "each" [.int 2] (some (.block [.req "x"] [] plusX))) hint
#guard !validateD (.send (some (.array [.int 1])) "map" [] (some (.block [.req "x"] [] plusX))) hint
#guard !validateD (.send (some (.array [.int 1])) "each" [] none) hint
#guard !validateD (each (.nxt (some (.int 1)))) (hint (.intLit 1))
#guard (check 100 [] each hint { ctx0 with neg := { ctx0.neg with declared := ["each"] } }).isNone

-- A hidden nil caller slot cannot receive the Integer parameter's type.
#guard validateD (.seq [.vasgn .lvar "x" .nil, each, .var .lvar "x"])
  (.flow (.seq [.vasgn .lvar "x" .nilLit, .eachBlock arrayHint plusHint, .var .lvar "x"]))
#guard !validateD (.seq [.vasgn .lvar "x" .nil, each, plusX])
  (.flow (.seq [.vasgn .lvar "x" .nilLit, .eachBlock arrayHint plusHint, plusHint]))

-- Stable writes to a live capture are admitted; changing its type is rejected.
#guard validateD (.seq [.vasgn .lvar "y" (.int 0), each (.vasgn .lvar "y" (.int 7))])
  (.flow (.seq [.vasgn .lvar "y" (.intLit 0), .eachBlock arrayHint (.vasgn .lvar "y" (.intLit 7))]))
#guard !validateD (.seq [.vasgn .lvar "y" (.int 0), each (.vasgn .lvar "y" .nil)])
  (.flow (.seq [.vasgn .lvar "y" (.intLit 0), .eachBlock arrayHint (.vasgn .lvar "y" .nilLit)]))

-- Parameter/block-local shadowing is distinct from a write to a capture.
#guard validateD (.seq [.vasgn .lvar "y" (.int 0), each (.vasgn .lvar "y" .nil) (.array [.int 1]) [.req "x"] ["y"]])
  (.flow (.seq [.vasgn .lvar "y" (.intLit 0), .eachBlock arrayHint (.vasgn .lvar "y" .nilLit)]))
end Checker.EachCheckControls
