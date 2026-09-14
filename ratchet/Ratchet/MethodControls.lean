import Ratchet.Check

/-! End-to-end method controls. An accepted declaration alone is not a call control. -/
namespace Ratchet

private def incBody : Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def incProof : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
private def inc : Expr := .def' "inc" [.req "x"] incBody
private def incCert : Deriv := .defDecl "inc" [("x", .int)] .int incProof

private def runInc (args : List Expr) (ds : List Deriv) (ret : Ty := .int) : Bool :=
  validateD (.seq [inc, .send none "inc" args none])
    (.seq [incCert, .callSig "inc" ds ret])

#guard runInc [.int 2] [.intLit 2]
#guard !runInc [] []
#guard !runInc [.int 2, .int 3] [.intLit 2, .intLit 3]
#guard !runInc [.str "bad"] [.strLit "bad"]
#guard !runInc [.int 2] [.intLit 2] .bool
#guard !validateD (.seq [inc, .send none "other" [.int 2] none])
  (.seq [incCert, .callSig "inc" [.intLit 2] .int])

-- The uncalled declaration is checked too, but this is not the sole positive control.
#guard validateD inc incCert
#guard !validateD inc (.defDecl "inc" [("x", .nilable .int)] .int incProof)
#guard !validateD (.seq [inc, .send none "inc" [.int 2] none])
  (.seq [.defDecl "inc" [("x", .nilable .int)] .int incProof, .callSig "inc" [.intLit 2] .int])
#guard !validateD inc (.defDecl "inc" [("x", .int)] .bool incProof)
#guard !validateD (.def' "bad" [] (.send none "missing" [] none))
  (.defDecl "bad" [] .int (.callSig "missing" [] .int))
-- A recursive signature cannot certify itself.
#guard !validateD (.def' "loop" [] (.send none "loop" [] none))
  (.defDecl "loop" [] .int (.callSig "loop" [] .int))

#guard validateD (.seq [.def' "get5" [] (.int 5), .send none "get5" [] none])
  (.seq [.defDecl "get5" [] .int (.intLit 5), .callSig "get5" [] .int])

-- Caller locals do not supply body bindings; body writes do not retype caller locals.
private def localBody : Expr := .seq [.vasgn .lvar "y" incBody, .var .lvar "y"]
private def localProof : Deriv := .seq [.vasgn .lvar "y" incProof, .var .lvar "y"]
#guard validateD (.seq [.vasgn .lvar "x" (.str "caller"),
    .def' "local_inc" [.req "x"] localBody, .send none "local_inc" [.int 2] none,
    .send (some (.var .lvar "x")) "length" [] none])
  (.seq [.vasgn .lvar "x" (.strLit "caller"),
    .defDecl "local_inc" [("x", .int)] .int localProof, .callSig "local_inc" [.intLit 2] .int,
    .prim (.var .lvar "x") "length" [] (.cls "String") .int])

-- The entire nullable domain is allowed when the body genuinely handles it.
#guard validateD (.seq [.def' "identity" [.req "x"] (.var .lvar "x"),
    .send none "identity" [.if' .tru (.int 1) (some .nil)] none])
  (.seq [.defDecl "identity" [("x", .nilable .int)] (.nilable .int) (.var .lvar "x"),
    .callSig "identity" [.ifD .truLit (.intLit 1) (some .nilLit) (.nilable .int)] (.nilable .int)])

-- Argument assignments retain the checked table/cache in evaluation order.
#guard validateD (.seq [inc, .send none "inc" [.vasgn .lvar "a" (.int 3)] none,
    .send none "inc" [.var .lvar "a"] none])
  (.seq [incCert, .callSig "inc" [.vasgn .lvar "a" (.intLit 3)] .int,
    .callSig "inc" [.var .lvar "a"] .int])

-- A second installation makes this first cache entry stale; do not cast its proof.
#guard !validateD (.seq [inc, .def' "later" [] (.int 0), .send none "inc" [.int 1] none])
  (.seq [incCert, .defDecl "later" [] .int (.intLit 0), .callSig "inc" [.intLit 1] .int])
#guard !validateD (.seq [inc, .def' "inc" [.req "x"] (.str "changed"),
    .send none "inc" [.int 1] none])
  (.seq [incCert, .defDecl "inc" [("x", .int)] (.cls "String") (.strLit "changed"),
    .callSig "inc" [.intLit 1] .int])

end Ratchet
