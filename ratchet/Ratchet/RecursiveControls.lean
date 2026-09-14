import Ratchet.Check

/-! Recursive bodies are checked over the annotated domain, not the final call's values. -/
namespace Ratchet.RecursiveControl

def params : Env := [("n", .int)]
def n : Expr := .var .lvar "n"
def dn : Deriv := .var .lvar "n"
def smaller : Expr := .send (some n) "-" [.int 1] none
def smallerProof : Deriv := .prim dn "-" [.intLit 1] .int .int
def body : Expr := .if' (.send (some n) "<=" [.int 1] none) (.int 1)
  (some (.send (some n) "*" [.send none "fact" [smaller] none] none))
def bodyProof : Deriv := .ifD (.prim dn "<=" [.intLit 1] .int .bool) (.intLit 1)
  (some (.prim dn "*" [.callSig "fact" [smallerProof] .int] .int .int)) .int
def decl : Defn := ⟨"fact", [.req "n"], body⟩
def definition : Expr := .def' decl.name decl.params decl.body
def cert : Deriv := .defDecl "fact" params .int bodyProof
def program : Expr := .seq [definition, .send none "fact" [.int 4] none]
def programCert : Deriv := .seq [cert, .callSig "fact" [.intLit 4] .int]

#guard validateD definition cert
#guard validateD program programCert
#guard (check fuelD [] program programCert).map (·.ty) == some .int
#guard !validateD definition (.defDecl "fact" [("n", .nilable .int)] .int bodyProof)
#guard !validateD program (.seq [
  .defDecl "fact" [("n", .nilable .int)] .int bodyProof, .callSig "fact" [.intLit 4] .int])
#guard !validateD definition (.defDecl "fact" params .bool bodyProof)
#guard !validateD (.seq [definition, .send none "fact" [.str "bad"] none])
  (.seq [cert, .callSig "fact" [.strLit "bad"] .int])

-- An invalid base branch rejects even if this call only visits the recursive branch.
private def branchBody (base : Expr) : Expr := .if' .fls base
  (some (.send none "branch" [n] none))
private def branchProof (base : Deriv) (ret : Ty := .int) : Deriv :=
  .ifD .flsLit base (some (.callSig "branch" [dn] .int)) ret
#guard validateD (.seq [.def' "branch" [.req "n"] (branchBody (.int 1)),
    .send none "branch" [.int 0] none])
  (.seq [.defDecl "branch" params .int (branchProof (.intLit 1)), .callSig "branch" [.intLit 0] .int])
#guard !validateD (.def' "branch" [.req "n"] (branchBody (.str "bad")))
  (.defDecl "branch" params .int (branchProof (.strLit "bad")))
#guard !validateD (.def' "branch" [.req "n"] (branchBody (.str "bad")))
  (.defDecl "branch" params .int (branchProof (.intLit 1)))

private def selfBody (args : List Expr) : Expr := .def' "self_call" [.req "n"]
  (.send none "self_call" args none)
private def selfCert (args : List Deriv) (ret : Ty := .int) (name := "self_call") : Deriv :=
  .defDecl "self_call" params .int (.callSig name args ret)
#guard validateD (selfBody [n]) (selfCert [dn])
#guard !validateD (selfBody []) (selfCert [])
#guard !validateD (selfBody [n, n]) (selfCert [dn, dn])
#guard !validateD (selfBody [.str "bad"]) (selfCert [.strLit "bad"])
#guard !validateD (selfBody [n]) (selfCert [dn] .bool)
#guard !validateD (selfBody [n]) (selfCert [dn] .int "other")

-- Refresh reconstructs the scoped proof before a later method may consume it.
#guard validateD (.seq [definition,
    .def' "call_fact" [.req "n"] (.send none "fact" [n] none),
    .send none "call_fact" [.int 4] none])
  (.seq [cert, .defDecl "call_fact" params .int (.callSig "fact" [dn] .int),
    .callSig "call_fact" [.intLit 4] .int])
-- Replaying under an invalidated primitive dispatch context must still reject.
#guard !validateD (.seq [definition, .def' "*" [.req "n"] (.str "changed")])
  (.seq [cert, .defDecl "*" params (.cls "String") (.strLit "changed")])

end Ratchet.RecursiveControl
