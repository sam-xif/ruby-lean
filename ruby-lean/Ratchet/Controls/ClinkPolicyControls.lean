import Ratchet.Check.Check

namespace Ratchet

-- Definitions still check the entire body, even if never called.
private def identityDefinition : Expr := .def' "identity" [.req "x"] (.var .lvar "x")
private def identityDefinitionHint : Deriv :=
  .defDecl "identity" [("x", .int)] .int (.var .lvar "x")
#guard validateD identityDefinition identityDefinitionHint == ["defDecl", "var"].all clinkEnabled
#guard !validateDWith (fun r => clinkEnabled r && r != "defDecl")
  identityDefinition identityDefinitionHint
#guard !validateDWith (fun r => clinkEnabled r && r != "var")
  identityDefinition identityDefinitionHint
#guard !validateD identityDefinition (.defDecl "identity" [("y", .int)] .int (.var .lvar "x"))
#guard !validateD (.def' "bad" [] (.str "wrong")) (.defDecl "bad" [] .int (.strLit "wrong"))
#guard !validateD (.def' "bad" [] (.send (some .nil) "+" [.int 1] none))
  (.defDecl "bad" [] .int (.prim .nilLit "+" [.intLit 1] .int .int))

-- Ordinary calls retain body, argument and companion checks.
private def identityCall : Expr :=
  .seq [identityDefinition, .send none "identity" [.int 7] none]
private def identityCallHint : Deriv :=
  .seq [identityDefinitionHint, .callSig "identity" [.intLit 7] .int]
#guard validateD identityCall identityCallHint ==
  ["seq", "DJudgeSeq.cons", "DJudgeSeq.last", "defDecl", "var", "callSig",
    "intLit", "DJudgeAll.nil", "DJudgeAll.cons"].all clinkEnabled
#guard !validateDWith (fun r => clinkEnabled r && r != "callSig") identityCall identityCallHint
#guard !validateDWith (fun r => clinkEnabled r && r != "DJudgeAll.nil") identityCall identityCallHint
#guard !validateDWith (fun r => clinkEnabled r && r != "DJudgeAll.cons") identityCall identityCallHint
#guard !validateDWith (fun r => clinkEnabled r && r != "var") identityCall identityCallHint
#guard !validateD (.seq [identityDefinition, .send none "identity" [.nil] none])
  (.seq [identityDefinitionHint, .callSig "identity" [.nilLit] .int])
#guard !validateD (.seq [identityDefinition, .send none "identity" [] none])
  (.seq [identityDefinitionHint, .callSig "identity" [] .int])
#guard !validateD identityCall (.seq [identityDefinitionHint, .callSig "identity" [.intLit 7] .bool])
#guard !validateDWith (fun _ => true) (.def' "to_s" [] (.int 1))
  (.defDecl "to_s" [] .int (.intLit 1))

-- Calling an older definition after installing a second preserves its code row.
#guard validateD
  (.seq [identityDefinition, .def' "other" [] (.int 2), .send none "identity" [.int 7] none])
  (.seq [identityDefinitionHint, .defDecl "other" [] .int (.intLit 2),
    .callSig "identity" [.intLit 7] .int]) ==
  ["seq", "DJudgeSeq.cons", "DJudgeSeq.last", "defDecl", "var", "callSig",
    "intLit", "DJudgeAll.nil", "DJudgeAll.cons"].all clinkEnabled

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

-- Ruby tests truthiness; both branches are checked regardless of the condition.
#guard validateD (.if' .nil (.int 1) (some (.int 2)))
  (.ifD .nilLit (.intLit 1) (some (.intLit 2)) .int) ==
  ["if'", "nilLit", "intLit"].all clinkEnabled
#guard !validateD (.if' .nil (.int 1) (some (.int 2)))
  (.ifD .nilLit (.intLit 3) (some (.intLit 2)) .int)
#guard !validateD (.if' .tru (.int 1) (some (.var .lvar "missing")))
  (.ifD .truLit (.intLit 1) (some (.var .lvar "missing")) .int)
#guard validateD (.if' .fls (.int 1) none)
  (.ifD .flsLit (.intLit 1) none (.nilable .int)) ==
  ["ifNoElse", "flsLit", "intLit"].all clinkEnabled
#guard !validateD (.if' .fls (.int 1) none) (.ifD .flsLit (.intLit 1) none .int)
#guard !validateDWith (fun r => clinkEnabled r && r != "ifNoElse")
  (.if' .fls (.int 1) none) (.ifD .flsLit (.intLit 1) none (.nilable .int))
#guard !validateD (.seq [.vasgn .lvar "x" (.int 1),
    .if' .tru (.vasgn .lvar "x" .nil) none,
    .send (some (.var .lvar "x")) "+" [.int 1] none])
  (.seq [.vasgn .lvar "x" (.intLit 1),
    .ifD .truLit (.vasgn .lvar "x" .nilLit) none .nilT,
    .prim (.var .lvar "x") "+" [.intLit 1] .int .int])

-- The bare-name escape rule is guarded and preserves the syntactic call site.
#guard validateD (.vcall "x") (.bareName "x") == clinkEnabled "bareName"
#guard !validateD (.vcall "y") (.bareName "y")
#guard !validateD (.send none "x" [] none) (.bareName "x")
#guard !validateDWith (fun _ => true)
  (.seq [.def' "x" [] (.int 1), .vcall "x"])
  (.seq [.defDecl "x" [] .int (.intLit 1), .bareName "x"])

-- Collection admission checks exact children, joins and companion permissions.
#guard validateD (.array []) (.arrayLit [] .never) ==
  ["arrayLit", "DJudgeAll.nil"].all clinkEnabled
#guard !validateD (.array []) (.arrayLit [] .any)
#guard validateD (.array [.vasgn .lvar "x" (.int 1), .var .lvar "x"])
  (.arrayLit [.vasgn .lvar "x" (.intLit 1), .var .lvar "x"] .int) ==
  ["arrayLit", "DJudgeAll.nil", "DJudgeAll.cons", "vasgn", "var", "intLit"].all clinkEnabled
#guard !validateD (.array [.int 1]) (.arrayLit [.intLit 2] .int)
#guard !validateD (.array [.int 1]) (.arrayLit [.intLit 1] .bool)
#guard !validateD (.array [.var .lvar "x", .vasgn .lvar "x" (.int 1)])
  (.arrayLit [.var .lvar "x", .vasgn .lvar "x" (.intLit 1)] .int)
#guard (check 100 [("f", .arrow0 .int)] (.array [.var .lvar "f"])
  (.arrayLit [.var .lvar "f"] (.arrow0 .int))).isNone
#guard validateD (.hash []) (.hashLit [] [] .never .never) ==
  ["hashLit", "DJudgePairs.nil"].all clinkEnabled
private def duplicateHash : Expr := .hash [(.sym "k", .int 1), (.sym "k", .int 2)]
private def duplicateHashHint : Deriv :=
  .hashLit [.symLit "k", .symLit "k"] [.intLit 1, .intLit 2] .sym .int
#guard validateD duplicateHash duplicateHashHint ==
  ["hashLit", "DJudgePairs.nil", "DJudgePairs.cons", "symLit", "intLit"].all clinkEnabled
#guard !validateDWith (fun r => clinkEnabled r && r != "DJudgePairs.cons")
  duplicateHash duplicateHashHint
#guard !validateDWith (fun r => clinkEnabled r && r != "DJudgePairs.nil")
  duplicateHash duplicateHashHint
#guard !validateD (.hash [(.sym "k", .int 1)]) (.hashLit [.symLit "k"] [] .sym .int)
#guard !validateD (.hash [(.sym "k", .int 1)])
  (.hashLit [.symLit "k"] [.intLit 2] .sym .int)
#guard !validateD (.hash [(.sym "k", .int 1)])
  (.hashLit [.symLit "k"] [.intLit 1] .sym .bool)
#guard validateD (.hash [(.vasgn .lvar "x" (.int 1), .var .lvar "x")])
  (.hashLit [.vasgn .lvar "x" (.intLit 1)] [.var .lvar "x"] .int .int) ==
  ["hashLit", "DJudgePairs.nil", "DJudgePairs.cons", "vasgn", "var", "intLit"].all clinkEnabled

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
#guard validateD (.seq [method, .send none "get5" [] none])
  (.seq [methodHint, .callSig "get5" [] .int]) ==
  ["seq", "DJudgeSeq.cons", "DJudgeSeq.last", "defDecl", "intLit", "callSig",
    "DJudgeAll.nil"].all clinkEnabled
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

-- Active classDecl: a literal body is accepted; builtin/reserved and reopened names are not.
private def literalClass : Expr := .class' "Box" none (.int 7)
private def literalClassHint : Deriv := .classDecl "Box" none (.intLit 7)
#guard validateD literalClass literalClassHint
#guard !validateDWith (fun r => clinkEnabled r && r != "classDecl") literalClass literalClassHint
#guard !validateD (.class' "String" none (.int 7)) (.classDecl "String" none (.intLit 7))
#guard !validateD (.class' "Object" none (.int 7)) (.classDecl "Object" none (.intLit 7))
-- A second declaration is not fresh; only the reopen rule admits it.
#guard !validateDWith (fun r => clinkEnabled r && r != "classReopen")
  (.seq [literalClass, literalClass]) (.seq [literalClassHint, literalClassHint])
#guard validateD (.seq [literalClass, literalClass]) (.seq [literalClassHint, literalClassHint])
#guard validateD (.seq [literalClass, .class' "Pair" none (.int 1)])
  (.seq [literalClassHint, .classDecl "Pair" none (.intLit 1)])

-- Active constClass: only a class declared earlier in the program is readable.
#guard validateD (.seq [literalClass, .const "Box"]) (.seq [literalClassHint, .constCls "Box"])
#guard !validateDWith (fun r => clinkEnabled r && r != "constClass")
  (.seq [literalClass, .const "Box"]) (.seq [literalClassHint, .constCls "Box"])
#guard !validateD (.seq [.const "Box", literalClass]) (.seq [.constCls "Box", literalClassHint])
#guard !validateD (.const "Box") (.constCls "Box")

-- Primitive rows Integer#<=>, Integer#nil?, Symbol#to_s, Symbol#==.
#guard validateD (.send (some (.int 1)) "<=>" [.int 2] none) (.prim (.intLit 1) "<=>" [.intLit 2] .int .int)
#guard !validateD (.send (some (.int 1)) "<=>" [.str "a"] none)
  (.prim (.intLit 1) "<=>" [.strLit "a"] .int .int)
#guard !validateD (.send (some (.int 1)) "<=>" [.int 2] none) (.prim (.intLit 1) "<=>" [.intLit 2] .int .bool)
#guard validateD (.send (some (.int 1)) "nil?" [] none) (.prim (.intLit 1) "nil?" [] .int .bool)
#guard !validateD (.send (some .nil) "nil?" [] none) (.prim .nilLit "nil?" [] .nilT .bool)
#guard validateD (.send (some (.sym "a")) "to_s" [] none) (.prim (.symLit "a") "to_s" [] .sym (.cls "String"))
#guard validateD (.send (some (.sym "a")) "==" [.int 1] none) (.prim (.symLit "a") "==" [.intLit 1] .sym .bool)
#guard !validateD (.send (some (.sym "a")) "length" [] none) (.prim (.symLit "a") "length" [] .sym .int)

-- Primitive rows Array#length and String#start_with?.
#guard validateD (.send (some (.array [.int 1])) "length" [] none)
  (.prim (.arrayLit [.intLit 1] .int) "length" [] (.arrayOf .int) .int)
#guard !validateD (.send (some (.array [.int 1])) "length" [] none)
  (.prim (.arrayLit [.intLit 1] .int) "length" [] (.arrayOf .int) .bool)
#guard validateD (.send (some (.str "ab")) "start_with?" [.str "a"] none)
  (.prim (.strLit "ab") "start_with?" [.strLit "a"] (.cls "String") .bool)
#guard !validateD (.send (some (.str "ab")) "start_with?" [.int 1] none)
  (.prim (.strLit "ab") "start_with?" [.intLit 1] (.cls "String") .bool)

-- Primitive row Hash#key?.
#guard validateD (.send (some (.hash [(.str "a", .int 1)])) "key?" [.str "a"] none)
  (.prim (.hashLit [.strLit "a"] [.intLit 1] (.cls "String") .int) "key?" [.strLit "a"]
    (.hashOf (.cls "String") .int) .bool)
#guard !validateD (.send (some (.hash [(.str "a", .int 1)])) "key?" [] none)
  (.prim (.hashLit [.strLit "a"] [.intLit 1] (.cls "String") .int) "key?" []
    (.hashOf (.cls "String") .int) .bool)

-- Active memberDef: a class-body def checks its body; auto-private and hook names are rejected.
private def memberClass (n : String) : Expr := .class' "Box" none (.def' n [] (.int 1))
private def memberHint (n : String) : Deriv := .classDecl "Box" none (.defDecl n [] .int (.intLit 1))
#guard validateD (memberClass "get") (memberHint "get")
#guard !validateDWith (fun r => clinkEnabled r && r != "memberDef") (memberClass "get") (memberHint "get")
#guard !validateD (memberClass "get") (.classDecl "Box" none (.defDecl "get" [] .bool (.intLit 1)))
#guard ["initialize_copy", "initialize_dup", "initialize_clone", "respond_to_missing?",
  "const_added", "inherited", "method_added", "method_missing", "new"].all fun n =>
  !validateD (memberClass n) (memberHint n)

-- Active newDefault: zero-argument construction of a declared class without initialize.
private def newBox : Expr := .send (some (.const "Box")) "new" [] none
#guard validateD (.seq [memberClass "get", newBox])
  (.seq [memberHint "get", .newInst "Box" [] (.inst "Box" .ivar0)])
#guard !validateDWith (fun r => clinkEnabled r && r != "newDefault") (.seq [memberClass "get", newBox])
  (.seq [memberHint "get", .newInst "Box" [] (.inst "Box" .ivar0)])
#guard !validateD (.seq [memberClass "get", .send (some (.const "Box")) "new" [.int 1] none])
  (.seq [memberHint "get", .newInst "Box" [.intLit 1] (.inst "Box" .ivar0)])
#guard !validateD newBox (.newInst "Box" [] (.inst "Box" .ivar0))

-- Active callMethodSig: Box.new.get (rung 069's shape); wrong result/unknown method rejected.
private def callGet (n : String) : Expr := .send (some newBox) n [] none
#guard validateD (.seq [memberClass "get", callGet "get"])
  (.seq [memberHint "get", .callMethodSig (.newInst "Box" [] (.inst "Box" .ivar0)) "get" [] .int])
#guard !validateDWith (fun r => clinkEnabled r && r != "callMethodSig") (.seq [memberClass "get", callGet "get"])
  (.seq [memberHint "get", .callMethodSig (.newInst "Box" [] (.inst "Box" .ivar0)) "get" [] .int])
#guard !validateD (.seq [memberClass "get", callGet "get"])
  (.seq [memberHint "get", .callMethodSig (.newInst "Box" [] (.inst "Box" .ivar0)) "get" [] .bool])
#guard !validateD (.seq [memberClass "get", callGet "other"])
  (.seq [memberHint "get", .callMethodSig (.newInst "Box" [] (.inst "Box" .ivar0)) "other" [] .int])

-- Active ivarRead: an unset ivar in a method body reads as nil (rung 070's shape).
private def revealClass : Expr := .class' "Box" none (.def' "reveal" [] (.var .ivar "@secret"))
#guard validateD (.seq [revealClass, callGet "reveal"])
  (.seq [.classDecl "Box" none (.defDecl "reveal" [] .nilT (.ivarRead "@secret" .nilT)),
    .callMethodSig (.newInst "Box" [] (.inst "Box" (.ivarCons "@secret" .nilT .ivar0))) "reveal" [] .nilT])
#guard !validateD (.seq [revealClass, callGet "reveal"])
  (.seq [.classDecl "Box" none (.defDecl "reveal" [] .int (.ivarRead "@secret" .int)),
    .callMethodSig (.newInst "Box" [] (.inst "Box" .ivar0)) "reveal" [] .int])

-- Active initDef/newInst + InitJudge: Box.new(1) through a user initializer (rung 062's shape).
private def initClass : Expr := .class' "Box" none
  (.def' "initialize" [.req "n"] (.vasgn .ivar "@n" (.var .lvar "n")))
private def initHint (t : Ty) : Deriv := .classDecl "Box" none
  (.defDecl "initialize" [("n", .int)] t (.ivarAsgn "@n" (.var .lvar "n")))
private def newBoxArg (a : Expr) : Expr := .send (some (.const "Box")) "new" [a] none
private def initTy : Ty := .inst "Box" (.ivarCons "@n" .int .ivar0)
#guard validateD (.seq [initClass, newBoxArg (.int 1)]) (.seq [initHint .int, .newInst "Box" [.intLit 1] initTy])
#guard ["initDef", "newInst", "InitJudge.ivarAsgn", "InitJudge.var"].all fun r =>
  !validateDWith (fun q => clinkEnabled q && q != r) (.seq [initClass, newBoxArg (.int 1)])
    (.seq [initHint .int, .newInst "Box" [.intLit 1] initTy])
#guard !validateD (.seq [initClass, newBoxArg (.str "x")]) (.seq [initHint .int, .newInst "Box" [.strLit "x"] initTy])
#guard !validateD (.seq [initClass, .send (some (.const "Box")) "new" [] none]) (.seq [initHint .int, .newInst "Box" [] initTy])
#guard !validateD (.seq [initClass, newBoxArg (.int 1)]) (.seq [initHint .nilT, .newInst "Box" [.intLit 1] initTy])
#guard !validateD (.seq [initClass, newBoxArg (.int 1)])
  (.seq [initHint .int, .newInst "Box" [.intLit 1] (.inst "Box" (.ivarCons "@n" .nilT .ivar0))])

-- Active vcallMethodSig: a bare-name self call inside an instance method (rung 064's shape).
private def vcallClass (callee : String) : Expr := .class' "Box" none (.seq [
  .def' "get" [] (.int 1), .def' "twice" [] (.vcall callee)])
private def vcallHint (callee : String) (t : Ty) : Deriv := .classDecl "Box" none (.seq [
  .defDecl "get" [] .int (.intLit 1), .defDecl "twice" [] t (.callSig callee [] t)])
private def vcallUse : Expr := .send (some newBox) "twice" [] none
private def vcallUseHint (t : Ty) : Deriv := .callMethodSig (.newInst "Box" [] (.inst "Box" .ivar0)) "twice" [] t
#guard validateD (.seq [vcallClass "get", vcallUse]) (.seq [vcallHint "get" .int, vcallUseHint .int])
#guard !validateDWith (fun r => clinkEnabled r && r != "vcallMethodSig") (.seq [vcallClass "get", vcallUse])
  (.seq [vcallHint "get" .int, vcallUseHint .int])
#guard !validateD (.seq [vcallClass "get", vcallUse]) (.seq [vcallHint "get" .bool, vcallUseHint .bool])
#guard !validateD (.seq [vcallClass "nope", vcallUse]) (.seq [vcallHint "nope" .int, vcallUseHint .int])

-- Active moduleDecl: a fresh module scope returns its body's value.
#guard validateD (.module' "M" (.int 7)) (.moduleDecl "M" (.intLit 7))
#guard !validateDWith (fun r => clinkEnabled r && r != "moduleDecl") (.module' "M" (.int 7)) (.moduleDecl "M" (.intLit 7))
#guard !validateD (.module' "M" (.int 7)) (.moduleDecl "M" (.strLit "7"))
#guard !validateD (.seq [.module' "M" (.int 7), .module' "M" (.int 8)])
  (.seq [.moduleDecl "M" (.intLit 7), .moduleDecl "M" (.intLit 8)])

-- Active singletonDef/callSingleton: M.f(1) through a module's def self.f (rung 078's shape).
private def modF (n : String) : Expr := .module' "M" (.defs .self' n [.req "x"] (.var .lvar "x"))
private def modH (n : String) (t : Ty) : Deriv := .moduleDecl "M" (.defDecl n [("x", .int)] t (.var .lvar "x"))
private def callF (n : String) : Expr := .send (some (.const "M")) n [.int 1] none
private def callH (n : String) (t : Ty) : Deriv := .callSingleton (.constCls "M") n [.intLit 1] t
#guard validateD (.seq [modF "f", callF "f"]) (.seq [modH "f" .int, callH "f" .int])
#guard ["singletonDef", "callSingleton", "moduleDecl"].all fun r =>
  !validateDWith (fun q => clinkEnabled q && q != r) (.seq [modF "f", callF "f"]) (.seq [modH "f" .int, callH "f" .int])
#guard !validateD (.seq [modF "f", callF "f"]) (.seq [modH "f" .bool, callH "f" .bool])
-- def self.singleton_method_added would hijack later def-self hooks; top-level too.
#guard !validateD (modF "singleton_method_added") (modH "singleton_method_added" .int)
#guard !validateD (.def' "singleton_method_added" [.req "x"] (.var .lvar "x"))
  (.defDecl "singleton_method_added" [("x", .int)] .int (.var .lvar "x"))

-- Active newImplicit/instanceType/selfRead: P.make(1) factory (073) and P.new(1).me (076).
private def pTy : Ty := .inst "P" (.ivarCons "@x" .int .ivar0)
private def pCls : Expr := .class' "P" none (.seq [
  .def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x")),
  .def' "me" [] .self',
  .defs .self' "make" [.req "x"] (.send none "new" [.var .lvar "x"] none)])
private def pHint : Deriv := .classDecl "P" none (.seq [
  .defDecl "initialize" [("x", .int)] .any (.ivarAsgn "@x" (.var .lvar "x")),
  .defDecl "me" [] (.cls "P") .selfExpr,
  .defDecl "make" [("x", .int)] (.cls "P") (.newImplicit "P" [.var .lvar "x"] pTy)])
private def pMake : Expr := .send (some (.const "P")) "make" [.int 1] none
private def pMakeH : Deriv := .callSingleton (.constCls "P") "make" [.intLit 1] pTy
private def pMe : Expr := .send (some (.send (some (.const "P")) "new" [.int 1] none)) "me" [] none
private def pMeH : Deriv := .callMethodSig (.newInst "P" [.intLit 1] pTy) "me" [] pTy
#guard validateD (.seq [pCls, pMake]) (.seq [pHint, pMakeH])
#guard validateD (.seq [pCls, pMe]) (.seq [pHint, pMeH])
#guard ["newImplicit", "instanceType", "selfRead"].all fun r =>
  !validateDWith (fun q => clinkEnabled q && q != r) (.seq [pCls, pMake]) (.seq [pHint, pMakeH])
#guard !validateD (.seq [pCls, .send (some (.const "P")) "make" [.str "a"] none])
  (.seq [pHint, .callSingleton (.constCls "P") "make" [.strLit "a"] pTy])

-- Primitive rows Array#compact/uniq (209).
private def nilArr : Deriv := .arrayLit [.intLit 1, .nilLit] (.nilable .int)
#guard validateD (.send (some (.send (some (.array [.int 1, .nil])) "compact" [] none)) "uniq" [] none)
  (.prim (.prim nilArr "compact" [] (.arrayOf (.nilable .int)) (.arrayOf .int)) "uniq" []
    (.arrayOf .int) (.arrayOf .int))
#guard !validateD (.send (some (.array [.int 1, .nil])) "compact" [] none)
  (.prim nilArr "compact" [] (.arrayOf (.nilable .int)) (.arrayOf (.nilable .int)))
#guard !validateD (.send (some (.array [.int 1])) "uniq" [.int 1] none)
  (.prim (.arrayLit [.intLit 1] .int) "uniq" [.intLit 1] (.arrayOf .int) (.arrayOf .int))

-- Primitive rows Hash#fetch/1, /2 (203).
private def hA : Ratchet.Expr := .hash [(.str "a", .int 1)]
private def hAH : Deriv := .hashLit [.strLit "a"] [.intLit 1] (.cls "String") .int
private def hTy : Ty := .hashOf (.cls "String") .int
#guard validateD (.send (some (.send (some hA) "fetch" [.str "a"] none)) "+"
    [.send (some hA) "fetch" [.str "b", .int 0] none] none)
  (.prim (.prim hAH "fetch" [.strLit "a"] hTy .int) "+"
    [.prim hAH "fetch" [.strLit "b", .intLit 0] hTy .int] .int .int)
#guard !validateD (.send (some hA) "fetch" [.str "b", .str "x"] none)
  (.prim hAH "fetch" [.strLit "b", .strLit "x"] hTy .int)
#guard !validateD (.send (some hA) "fetch" [.str "b", .str "x"] none)
  (.prim hAH "fetch" [.strLit "b", .strLit "x"] hTy (.cls "String"))

-- Primitive row String#=== (197's case/when).
#guard validateD (.send (some (.str "gem")) "===" [.str "x"] none)
  (.prim (.strLit "gem") "===" [.strLit "x"] (.cls "String") .bool)
#guard !validateD (.send (some (.str "gem")) "===" [.int 1] none)
  (.prim (.strLit "gem") "===" [.intLit 1] (.cls "String") .bool)

-- Primitive row String#split (177).
#guard validateD (.send (some (.send (some (.str "a/b")) "split" [.str "/"] none)) "length" [] none)
  (.prim (.prim (.strLit "a/b") "split" [.strLit "/"] (.cls "String") (.arrayOf (.cls "String")))
    "length" [] (.arrayOf (.cls "String")) .int)
#guard !validateD (.send (some (.str "a/b")) "split" [.int 1] none)
  (.prim (.strLit "a/b") "split" [.intLit 1] (.cls "String") (.arrayOf (.cls "String")))

-- Active scalarIvarAsgn: 074's Integer field replacement; nil fields are excluded.
private def boxCls (rhs : Ratchet.Expr) : Ratchet.Expr := .class' "Box" none (.seq [
  .def' "initialize" [.req "size"] (.vasgn .ivar "@size" (.var .lvar "size")),
  .def' "grow" [] (.vasgn .ivar "@size" rhs)])
private def boxHint (fty : Ty) (rhs : Deriv) : Deriv := .classDecl "Box" none (.seq [
  .defDecl "initialize" [("size", fty)] .any (.ivarAsgn "@size" (.var .lvar "size")),
  .defDecl "grow" [] fty (.ivarAsgn "@size" rhs)])
private def boxTy (fty : Ty) : Ty := .inst "Box" (.ivarCons "@size" fty .ivar0)
private def growCall (fty : Ty) (arg : Deriv) : Deriv :=
  .callMethodSig (.newInst "Box" [arg] (boxTy fty)) "grow" [] fty
private def incr : Ratchet.Expr := .send (some (.var .ivar "@size")) "+" [.int 1] none
private def incrH : Deriv := .prim (.ivarRead "@size" .int) "+" [.intLit 1] .int .int
#guard validateD (.seq [boxCls incr, .send (some (.send (some (.const "Box")) "new" [.int 1] none)) "grow" [] none])
  (.seq [boxHint .int incrH, growCall .int (.intLit 1)])
#guard !validateDWith (fun q => clinkEnabled q && q != "scalarIvarAsgn")
  (.seq [boxCls incr, .send (some (.send (some (.const "Box")) "new" [.int 1] none)) "grow" [] none])
  (.seq [boxHint .int incrH, growCall .int (.intLit 1)])
#guard !validateD (.seq [boxCls .nil, .send (some (.send (some (.const "Box")) "new" [.nil] none)) "grow" [] none])
  (.seq [boxHint .nilT .nilLit, growCall .nilT .nilLit])
#guard !validateD (.seq [boxCls (.str "a"), .send (some (.send (some (.const "Box")) "new" [.int 1] none)) "grow" [] none])
  (.seq [boxHint .int (.strLit "a"), growCall .int (.intLit 1)])

-- Active subclassDecl (066): a subclass of a declared plain class overrides a method.
private def animal : Ratchet.Expr := .class' "Animal" none (.def' "speak" [] (.str "..."))
private def animalH : Deriv := .classDecl "Animal" none (.defDecl "speak" [] (.cls "String") (.strLit "..."))
private def dogP (sup : Ratchet.Expr) (rhs : Ratchet.Expr) : Ratchet.Expr := .seq [animal,
  .class' "Dog" (some sup) (.def' "speak" [] rhs),
  .send (some (.send (some (.const "Dog")) "new" [] none)) "speak" [] none]
private def dogH (parent : String) (rhs : Deriv) (t : Ty) : Deriv := .seq [animalH,
  .classDecl "Dog" (some parent) (.defDecl "speak" [] t rhs),
  .callMethodSig (.newInst "Dog" [] (.inst "Dog" .ivar0)) "speak" [] t]
#guard validateD (dogP (.const "Animal") (.str "Woof")) (dogH "Animal" (.strLit "Woof") (.cls "String"))
#guard !validateDWith (fun q => clinkEnabled q && q != "subclassDecl")
  (dogP (.const "Animal") (.str "Woof")) (dogH "Animal" (.strLit "Woof") (.cls "String"))
#guard !validateD (dogP (.const "Animal") (.int 1)) (dogH "Animal" (.intLit 1) (.cls "String"))
#guard !validateD (dogP (.const "Cat") (.str "Woof")) (dogH "Cat" (.strLit "Woof") (.cls "String"))
#guard !validateD (.seq [.module' "M" (.int 1), .class' "Dog" (some (.const "M")) (.int 1)])
  (.seq [.moduleDecl "M" (.intLit 1), .classDecl "Dog" (some "M") (.intLit 1)])

-- Active newInherited/callInherited (065): Dog inherits Animal's initializer and reader.
private def animalF : Ratchet.Expr := .class' "Animal" none (.seq [
  .def' "initialize" [.req "name"] (.vasgn .ivar "@name" (.var .lvar "name")),
  .def' "speak" [] (.var .ivar "@name")])
private def animalFH (t : Ty) : Deriv := .classDecl "Animal" none (.seq [
  .defDecl "initialize" [⟨"name", t⟩] .any (.ivarAsgn "@name" (.var .lvar "name")),
  .defDecl "speak" [] t (.ivarRead "@name" t)])
private def rexP (arg : Ratchet.Expr) : Ratchet.Expr := .seq [animalF,
  .class' "Dog" (some (.const "Animal")) .nil,
  .send (some (.send (some (.const "Dog")) "new" [arg] none)) "speak" [] none]
private def rexH (t : Ty) (arg : Deriv) : Deriv := .seq [animalFH t, .classDecl "Dog" (some "Animal") .nilLit,
  .callMethodSig (.newInst "Dog" [arg] (.inst "Dog" (.ivarCons "@name" t .ivar0))) "speak" [] t]
#guard validateD (rexP (.str "Rex")) (rexH (.cls "String") (.strLit "Rex"))
#guard ["newInherited", "callInherited"].all fun r =>
  !validateDWith (fun q => clinkEnabled q && q != r) (rexP (.str "Rex")) (rexH (.cls "String") (.strLit "Rex"))
#guard !validateD (rexP (.int 1)) (rexH (.cls "String") (.intLit 1))
#guard !validateD (rexP (.str "Rex")) (rexH .int (.strLit "Rex"))

-- Active InitJudge.superInit/InitJudgeAll (067): Triangle#initialize calls super(3).
private def shapeC : Ratchet.Expr := .class' "Shape" none (.seq [
  .def' "initialize" [.req "sides"] (.vasgn .ivar "@sides" (.var .lvar "sides")),
  .def' "sides" [] (.var .ivar "@sides")])
private def shapeH : Deriv := .classDecl "Shape" none (.seq [
  .defDecl "initialize" [⟨"sides", .int⟩] .any (.ivarAsgn "@sides" (.var .lvar "sides")),
  .defDecl "sides" [] .int (.ivarRead "@sides" .int)])
private def triP (args : List Ratchet.Expr) : Ratchet.Expr := .seq [shapeC,
  .class' "Triangle" (some (.const "Shape")) (.def' "initialize" [] (.super' args none)),
  .send (some (.send (some (.const "Triangle")) "new" [] none)) "sides" [] none]
private def triH (args : List Deriv) : Deriv := .seq [shapeH,
  .classDecl "Triangle" (some "Shape") (.defDecl "initialize" [] .any (.superInit args)),
  .callMethodSig (.newInst "Triangle" [] (.inst "Triangle" (.ivarCons "@sides" .int .ivar0))) "sides" [] .int]
#guard validateD (triP [.int 3]) (triH [.intLit 3])
#guard ["InitJudge.superInit", "InitJudgeAll.cons", "InitJudgeAll.nil"].all fun r =>
  !validateDWith (fun q => clinkEnabled q && q != r) (triP [.int 3]) (triH [.intLit 3])
#guard !validateD (triP [.str "three"]) (triH [.strLit "three"])
#guard !validateD (triP []) (triH [])

-- Active ifTruthy (125): `if x` narrows a nilable local in both branches.
private def truthyP (els : Ratchet.Expr) : Ratchet.Expr := .seq [
  .vasgn .lvar "a" (.array [.int 1, .int 2]),
  .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
  .if' (.var .lvar "x") (.send (some (.var .lvar "x")) "+" [.int 1] none) (some els)]
private def truthyH (els : Deriv) (j : Ty) : Deriv := .seq [
  .vasgn .lvar "a" (.arrayLit [.intLit 1, .intLit 2] .int),
  .vasgn .lvar "x" (.prim (.var .lvar "a") "[]" [.intLit 0] (.arrayOf .int) (.nilable .int)),
  .ifTruthy "x" (.prim (.var .lvar "x") "+" [.intLit 1] .int .int) els j]
#guard validateD (truthyP (.int 0)) (truthyH (.intLit 0) .int)
#guard !validateDWith (fun q => clinkEnabled q && q != "ifTruthy") (truthyP (.int 0)) (truthyH (.intLit 0) .int)
#guard !validateD (truthyP (.send (some (.var .lvar "x")) "+" [.int 1] none))
  (truthyH (.prim (.var .lvar "x") "+" [.intLit 1] .int .int) .int)

-- Active ifNilQuery (126): `if x.nil?` narrows a nilable Integer local.
private def nilQP (thn : Ratchet.Expr) : Ratchet.Expr := .seq [
  .vasgn .lvar "a" (.array [.int 1, .int 2]),
  .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 1] none),
  .if' (.send (some (.var .lvar "x")) "nil?" [] none) thn
    (some (.send (some (.var .lvar "x")) "+" [.int 10] none))]
private def nilQH (thn : Deriv) : Deriv := .seq [
  .vasgn .lvar "a" (.arrayLit [.intLit 1, .intLit 2] .int),
  .vasgn .lvar "x" (.prim (.var .lvar "a") "[]" [.intLit 1] (.arrayOf .int) (.nilable .int)),
  .ifNilQuery "x" thn (.prim (.var .lvar "x") "+" [.intLit 10] .int .int) .int]
#guard validateD (nilQP (.int 0)) (nilQH (.intLit 0))
#guard !validateDWith (fun q => clinkEnabled q && q != "ifNilQuery") (nilQP (.int 0)) (nilQH (.intLit 0))
#guard !validateD (nilQP (.send (some (.var .lvar "x")) "+" [.int 1] none))
  (nilQH (.prim (.var .lvar "x") "+" [.intLit 1] .int .int))

-- Active classReopen (109): a second `class Foo` adds a method to the existing class.
private def fooP (rhs : Ratchet.Expr) : Ratchet.Expr := .seq [
  .class' "Foo" none (.def' "a" [] (.int 1)), .class' "Foo" none (.def' "b" [] rhs),
  .send (some (.send (some (.const "Foo")) "new" [] none)) "b" [] none]
private def fooH (rhs : Deriv) (t : Ty) : Deriv := .seq [
  .classDecl "Foo" none (.defDecl "a" [] .int (.intLit 1)),
  .classDecl "Foo" none (.defDecl "b" [] t rhs),
  .callMethodSig (.newInst "Foo" [] (.inst "Foo" .ivar0)) "b" [] t]
#guard validateD (fooP (.int 2)) (fooH (.intLit 2) .int)
#guard !validateDWith (fun q => clinkEnabled q && q != "classReopen") (fooP (.int 2)) (fooH (.intLit 2) .int)
#guard !validateD (fooP (.str "x")) (fooH (.strLit "x") .int)

-- Active while' (184): a loop whose body keeps local types.
private def loopP (rhs : Ratchet.Expr) : Ratchet.Expr := .seq [
  .vasgn .lvar "i" (.int 0),
  .while' (.send (some (.var .lvar "i")) "<" [.int 3] none) (.vasgn .lvar "i" rhs),
  .var .lvar "i"]
private def loopH (rhs : Deriv) (t : Ty) : Deriv := .seq [
  .vasgn .lvar "i" (.intLit 0),
  .whileD (.prim (.var .lvar "i") "<" [.intLit 3] .int .bool) (.vasgn .lvar "i" rhs),
  .var .lvar "i"]
#guard validateD (loopP (.send (some (.var .lvar "i")) "+" [.int 1] none))
  (loopH (.prim (.var .lvar "i") "+" [.intLit 1] .int .int) .int)
#guard !validateDWith (fun q => clinkEnabled q && q != "while'")
  (loopP (.send (some (.var .lvar "i")) "+" [.int 1] none))
  (loopH (.prim (.var .lvar "i") "+" [.intLit 1] .int .int) .int)
#guard !validateD (loopP (.str "x")) (loopH (.strLit "x") (.cls "String"))

-- Active ifTruthyNoElse (134): `if y` without else narrows y in the then-branch only.
private def noElseP (thn : Ratchet.Expr) : Ratchet.Expr := .seq [
  .vasgn .lvar "y" (.send (some (.array [.int 1])) "[]" [.int 0] none),
  .if' (.var .lvar "y") thn none]
private def noElseH (thn : Deriv) (j : Ty) : Deriv := .seq [
  .vasgn .lvar "y" (.prim (.arrayLit [.intLit 1] .int) "[]" [.intLit 0] (.arrayOf .int) (.nilable .int)),
  .ifTruthyNoElse "y" thn j]
#guard validateD (noElseP (.send (some (.var .lvar "y")) "+" [.int 1] none))
  (noElseH (.prim (.var .lvar "y") "+" [.intLit 1] .int .int) (.nilable .int))
#guard !validateDWith (fun q => clinkEnabled q && q != "ifTruthyNoElse")
  (noElseP (.send (some (.var .lvar "y")) "+" [.int 1] none))
  (noElseH (.prim (.var .lvar "y") "+" [.intLit 1] .int .int) (.nilable .int))
#guard !validateD (noElseP (.send (some (.var .lvar "y")) "+" [.int 1] none))
  (noElseH (.prim (.var .lvar "y") "+" [.intLit 1] .int .int) .int)

-- Active flow rules: 087's stored zero-arity lambda call; the body's real type is checked.
private def lamProg (body : Ratchet.Expr) : Ratchet.Expr := .seq [
  .vasgn .lvar "f" (.send none "lambda" [] (some (.block [] [] body))),
  .send (some (.var .lvar "f")) "call" [] none]
private def lamHint (body : Deriv) (t : Ty) : Deriv :=
  .flow (.seq [.vasgn .lvar "f" .closureLiteral, .closureCall body t])
#guard validateD (lamProg (.int 1)) (lamHint (.intLit 1) .int)
#guard !validateD (lamProg (.int 1)) (lamHint (.intLit 1) (.cls "String"))
#guard ["flow", "DFlow.closureLiteral", "DFlow.call", "DFlow.vasgn"].all fun r =>
  !validateDWith (fun q => clinkEnabled q && q != r) (lamProg (.int 1)) (lamHint (.intLit 1) .int)
-- Active DFlow.prim (235): a primitive on a stored-lambda result after a same-type
-- reassignment of its capture; a String receiver claim or result is rejected.
private def capProg (x2 : Ratchet.Expr) : Ratchet.Expr := .seq [
  .vasgn .lvar "x" (.int 1), .vasgn .lvar "f" (.send none "lambda" [] (some (.block [] [] (.var .lvar "x")))),
  .vasgn .lvar "x" x2, .send (some (.send (some (.var .lvar "f")) "call" [] none)) "+" [.int 1] none]
private def capHint (x2 : Deriv) (t : Ty) : Deriv := .flow (.seq [
  .vasgn .lvar "x" (.intLit 1), .vasgn .lvar "f" .closureLiteral, .vasgn .lvar "x" x2,
  .prim (.closureCall (.var .lvar "x") t) "+" [.intLit 1] t t])
#guard validateD (capProg (.int 2)) (capHint (.intLit 2) .int)
#guard !validateDWith (fun q => clinkEnabled q && q != "DFlow.prim") (capProg (.int 2)) (capHint (.intLit 2) .int)
#guard !validateD (capProg (.str "a")) (capHint (.strLit "a") .int)
#guard !validateD (capProg (.int 2)) (capHint (.intLit 2) (.cls "String"))

-- Active each/map attached blocks (091/092): element type and result element are checked.
private def arr12 : Ratchet.Expr := .array [.int 1, .int 2]
private def arr12H : Deriv := .arrayLit [.intLit 1, .intLit 2] .int
private def eachP (body : Ratchet.Expr) : Ratchet.Expr :=
  .send (some arr12) "each" [] (some (.block [.req "x"] [] body))
private def mapP (body : Ratchet.Expr) : Ratchet.Expr :=
  .send (some arr12) "map" [] (some (.block [.req "x"] [] body))
private def xPlus1 : Ratchet.Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def xPlus1H : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
private def xToS : Ratchet.Expr := .send (some (.var .lvar "x")) "to_s" [] none
private def xToSH : Deriv := .prim (.var .lvar "x") "to_s" [] .int (.cls "String")
#guard validateD (eachP xPlus1) (.flow (.eachBlock arr12H xPlus1H))
#guard validateD (mapP xToS) (.flow (.mapBlock arr12H xToSH))
#guard !validateDWith (fun q => clinkEnabled q && q != "DFlow.each") (eachP xPlus1)
  (.flow (.eachBlock arr12H xPlus1H))
#guard !validateDWith (fun q => clinkEnabled q && q != "DFlow.map") (mapP xToS)
  (.flow (.mapBlock arr12H xToSH))
#guard !validateD (eachP (.send (some (.var .lvar "x")) "+" [.str "a"] none))
  (.flow (.eachBlock arr12H (.prim (.var .lvar "x") "+" [.strLit "a"] .int .int)))

-- Active yield rules (094): the block body is checked at the declared block types.
private def twiceP (blk : Ratchet.Expr) : Ratchet.Expr := .seq [
  .def' "twice" [] (.send (some (.yield' [.int 1])) "+" [.yield' [.int 2]] none),
  .send none "twice" [] (some (.block [.req "x"] [] blk))]
private def twiceH (blk : Deriv) : Deriv := .flow (.seq [
  .defBlock "twice" [] [.int] .int .int
    (.prim (.yieldArgs [.intLit 1]) "+" [.yieldArgs [.intLit 2]] .int .int),
  .callBlock "twice" blk .int])
private def x10 : Ratchet.Expr := .send (some (.var .lvar "x")) "*" [.int 10] none
private def x10H : Deriv := .prim (.var .lvar "x") "*" [.intLit 10] .int .int
#guard validateD (twiceP x10) (twiceH x10H)
#guard ["defBlock", "DFlow.callBlock", "DMethod.yieldOne"].all fun r =>
  !validateDWith (fun q => clinkEnabled q && q != r) (twiceP x10) (twiceH x10H)
#guard !validateD (twiceP (.str "a")) (twiceH (.strLit "a"))

#print axioms validateD_enabled
#print axioms validateD_typed
#print axioms Audit.DJudge.toRaw
end Ratchet
