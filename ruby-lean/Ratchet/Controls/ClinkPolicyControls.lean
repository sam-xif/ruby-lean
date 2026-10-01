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
