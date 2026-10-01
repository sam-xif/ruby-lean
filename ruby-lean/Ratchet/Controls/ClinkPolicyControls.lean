import Ratchet.Check.Check

namespace Ratchet

-- The actual verdict follows the shared clink policy for every supported rule.
#guard validateD (.int 7) (.intLit 7) == clinkEnabled "intLit"
#guard validateD (.flt 0) (.fltLit 0) == clinkEnabled "fltLit"
#guard validateD (.str "ok") (.strLit "ok") == clinkEnabled "strLit"
#guard validateD (.sym "ok") (.symLit "ok") == clinkEnabled "symLit"
#guard validateD .tru .truLit == clinkEnabled "truLit"
#guard validateD .fls .flsLit == clinkEnabled "flsLit"
#guard validateD .nil .nilLit == clinkEnabled "nilLit"

-- An enabled rule still checks the program against the exact certificate.
#guard !validateD (.int 7) (.intLit 8)
#guard !validateD (.int 7) .nilLit
#guard !validateD (.flt 0) (.fltLit 1)
#guard !validateD (.str "ok") (.strLit "bad")
#guard !validateD (.sym "ok") (.symLit "bad")

-- Companion rules and child rules must be permitted as well as the parent.
#guard validateD (.seq [.int 7]) (.seq [.intLit 7]) ==
  ["seq", "DJudgeSeq.last", "intLit"].all clinkEnabled
#guard validateD (.seq [.int 7, .int 8]) (.seq [.intLit 7, .intLit 8]) ==
  ["seq", "DJudgeSeq.cons", "DJudgeSeq.last", "intLit"].all clinkEnabled
#guard validateD (.int 7) (.flow (.intLit 7)) ==
  ["flow", "DFlow.intLit"].all clinkEnabled

private def sequenceRules (r : String) : Bool :=
  ["seq", "DJudgeSeq.last", "DJudgeSeq.cons", "intLit"].contains r
#guard validateDWith sequenceRules (.seq [.int 7, .int 8]) (.seq [.intLit 7, .intLit 8])
#guard !validateDWith (fun r => sequenceRules r && r != "seq")
  (.seq [.int 7]) (.seq [.intLit 7])
#guard !validateDWith (fun r => sequenceRules r && r != "DJudgeSeq.last")
  (.seq [.int 7]) (.seq [.intLit 7])
#guard !validateDWith (fun r => sequenceRules r && r != "intLit")
  (.seq [.int 7]) (.seq [.intLit 7])
#guard !validateDWith (fun r => sequenceRules r && r != "DJudgeSeq.cons")
  (.seq [.int 7, .int 8]) (.seq [.intLit 7, .intLit 8])

-- Sequence admission retains exact child, length and nonempty-body checks.
#guard !validateD (.seq [.int 7, .int 8]) (.seq [.intLit 7, .intLit 9])
#guard !validateD (.seq [.int 7, .int 8]) (.seq [.intLit 7])
#guard !validateD (.seq []) (.seq [])
#guard validateD (.seq [.seq [.int 7], .str "ok"])
  (.seq [.seq [.intLit 7], .strLit "ok"]) ==
  ["seq", "DJudgeSeq.cons", "DJudgeSeq.last", "intLit", "strLit"].all clinkEnabled

private def primitiveRules (r : String) : Bool :=
  ["prim", "intLit", "DJudgeAll.cons", "DJudgeAll.nil"].contains r
#guard validateDWith primitiveRules (.send (some (.int 1)) "+" [.int 2] none)
  (.prim (.intLit 1) "+" [.intLit 2] .int .int)
#guard !validateDWith (fun r => primitiveRules r && r != "DJudgeAll.nil")
  (.send (some (.int 1)) "+" [.int 2] none)
  (.prim (.intLit 1) "+" [.intLit 2] .int .int)
#guard !validateDWith (fun _ => true) (.send (some (.int 1)) "+" [.int 2] none)
  (.prim (.intLit 1) "+" [.intLit 3] .int .int)
#guard validateD (.send (some (.int 1)) "+" [.int 2] none)
  (.prim (.intLit 1) "+" [.intLit 2] .int .int) ==
  ["prim", "intLit", "DJudgeAll.cons", "DJudgeAll.nil"].all clinkEnabled
#guard !validateD (.send (some (.int 1)) "+" [.nil] none)
  (.prim (.intLit 1) "+" [.nilLit] .int .int)
#guard !validateD (.send (some (.int 1)) "+" [] none)
  (.prim (.intLit 1) "+" [] .int .int)
#guard !validateD (.send (some (.int 1)) "+" [.int 2] none)
  (.prim (.intLit 1) "+" [.intLit 2] .int .bool)

-- The receiver is saved before an argument overwrites its source binding.
private def savedReceiver : Expr := .send
  (some (.vasgn .lvar "x" (.int 1))) "+"
  [.seq [.vasgn .lvar "x" .nil, .int 2]] none
private def savedReceiverHint : Deriv := .prim
  (.vasgn .lvar "x" (.intLit 1)) "+"
  [.seq [.vasgn .lvar "x" .nilLit, .intLit 2]] .int .int
#guard validateD savedReceiver savedReceiverHint ==
  ["prim", "intLit", "nilLit", "vasgn", "seq", "DJudgeSeq.last", "DJudgeSeq.cons",
    "DJudgeAll.cons", "DJudgeAll.nil"].all clinkEnabled
#guard !validateDWith (fun r => clinkEnabled r && r != "vasgn") savedReceiver savedReceiverHint

-- Assignment threads the RHS state and permits later retyping of a local.
private def localRules := ["seq", "DJudgeSeq.last", "DJudgeSeq.cons", "var", "vasgn",
  "intLit", "nilLit"]
private def retypedLocal : Expr :=
  .seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" .nil, .var .lvar "x"]
private def retypedHint : Deriv :=
  .seq [.vasgn .lvar "x" (.intLit 1), .vasgn .lvar "x" .nilLit, .var .lvar "x"]
#guard validateD retypedLocal retypedHint == localRules.all clinkEnabled
#guard !validateDWith (fun r => localRules.contains r && r != "var") retypedLocal retypedHint
#guard !validateDWith (fun r => localRules.contains r && r != "vasgn") retypedLocal retypedHint
#guard !validateD (.var .lvar "missing") (.var .lvar "missing")
#guard !validateD (.vasgn .lvar "x" (.int 1)) (.vasgn .lvar "x" (.intLit 2))
#guard !validateD (.vasgn .ivar "@x" (.int 1)) (.vasgn .lvar "@x" (.intLit 1))
#guard validateD (.seq [.vasgn .lvar "x" (.vasgn .lvar "y" (.int 1)), .var .lvar "y"])
  (.seq [.vasgn .lvar "x" (.vasgn .lvar "y" (.intLit 1)), .var .lvar "y"]) ==
  ["seq", "DJudgeSeq.last", "DJudgeSeq.cons", "var", "vasgn", "intLit"].all clinkEnabled

-- Uncalled bodies and uniformly quantified callback witnesses are checked too.
private def method : Expr := .def' "get5" [] (.int 5)
private def methodHint : Deriv := .defDecl "get5" [] .int (.intLit 5)
#guard validateDWith (fun _ => true) method methodHint
#guard !validateDWith (fun r => r != "intLit") method methodHint
#guard validateDWith (fun _ => true)
  (.seq [method, .send none "get5" [] none])
  (.seq [methodHint, .callSig "get5" [] .int])
#guard !validateDWith (fun r => r != "intLit")
  (.seq [method, .send none "get5" [] none])
  (.seq [methodHint, .callSig "get5" [] .int])
#guard validateDWith (fun _ => true) method
  (.defBlock "get5" [] [.int] .int .int (.intLit 5))
#guard !validateDWith (fun r => r != "DMethod.ordinary") method
  (.defBlock "get5" [] [.int] .int .int (.intLit 5))
#guard !validateDWith (fun r => r != "intLit") method
  (.defBlock "get5" [] [.int] .int .int (.intLit 5))

-- Initializer judgments contribute their own trace, even when never invoked.
private def initializedClass : Expr := .class' "Box" none
  (.seq [.def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x"))])
private def initializedHint : Deriv := .classDecl "Box" none
  (.seq [.defDecl "initialize" [("x", .int)] .any
    (.ivarAsgn "@x" (.var .lvar "x"))])
#guard validateDWith (fun _ => true) initializedClass initializedHint
#guard !validateDWith (fun r => r != "InitJudge.var") initializedClass initializedHint
#guard !validateDWith (fun r => r != "InitJudge.ignoreResult") initializedClass initializedHint

#print axioms validateD_enabled
#print axioms validateD_typed
#print axioms Audit.DJudge.toRaw
end Ratchet
