/-! Source-controlled clink admission during semantic rebuilding. Names are the
constructor suffixes reported by the registry, not chronological clink numbers.
`none` enables the complete authoring family; `some [...]` is an exact allowlist.
Shared by the isolated checker and the semantic registry.
Denote/Clink/ActiveProofs.lean imports the selected semantic proofs. -/
namespace Ratchet

def clinkProfileName : String := "semantic-rebuild"

def clinkProfile : Option (List String) := some
  ["intLit", "fltLit", "strLit", "symLit", "truLit", "flsLit", "nilLit", "regexpLit",
   "seq", "DJudgeSeq.last", "DJudgeSeq.cons", "var", "vasgn", "vasgnAlias",
   "prim", "DJudgeAll.nil", "DJudgeAll.cons", "if'", "ifNoElse", "ifTruthy", "ifTruthyNoElse", "ifNilVar", "ifNilQueryNil", "ifNilQuery", "ifIsA", "ifIsAIvar", "ifCaseEq", "ifCaseEqVar", "ifAndVar", "dead", "widen", "sendUnion", "casgnTop", "constRead", "while'", "bareName",
   "arrayLit", "hashLit", "DJudgePairs.nil", "DJudgePairs.cons", "defDecl", "callSig", "defDeclOpt", "callSigOpt", "defDeclKw", "callSigKw", "defDeclKwOpt", "callSigKwOpt", "defDeclRest", "callSigRest",
   "recursive", "DJudgeRec.embed", "DJudgeRec.prim", "DJudgeRec.if'", "DJudgeRec.selfCall",
   "DJudgeRecAll.nil", "DJudgeRecAll.cons", "classDecl", "classReopen", "subclassDecl", "newInherited", "callInherited", "constClass", "memberDef", "newDefault", "callMethodSig", "ivarRead",
   "initDef", "newInst", "InitJudge.intLit", "InitJudge.var", "InitJudge.ivarAsgn", "InitJudge.seq",
   "InitJudge.ignoreResult", "InitJudge.strLit", "InitJudge.widenL", "InitJudge.widenR", "InitJudge.ifVar", "InitJudgeSeq.last", "InitJudgeSeq.cons", "InitJudge.superInit",
   "InitJudgeAll.nil", "InitJudgeAll.cons", "vcallMethodSig", "moduleDecl",
   "singletonDef", "callSingleton", "callSingletonImplicit",
   "newImplicit", "instanceType", "selfRead", "scalarIvarAsgn",
   "flow", "DFlow.embed", "DFlow.intLit", "DFlow.nilLit", "DFlow.var", "DFlow.closureLiteral",
   "DFlow.vasgn", "DFlow.sequence", "DFlow.call", "DFlow.requiredCall", "DFlowSeq.last",
   "DFlowSeq.cons", "DFlowAll.nil", "DFlowAll.cons", "DFlow.each", "DFlow.map",
   "defBlock", "defBoundBlock", "DFlow.callBlock", "DFlow.callBoundBlock", "DFlow.prim",
   "DMethod.ordinary", "DMethod.vasgn", "DMethod.sequence", "DMethod.prim", "DMethod.yieldOne",
   "DMethodAll.nil", "DMethodAll.cons", "DMethodSeq.last", "DMethodSeq.cons",
   "DMethodFlow.embed", "DMethodFlow.intLit", "DMethodFlow.nilLit", "DMethodFlow.var",
   "DMethodFlow.vasgn", "DMethodFlow.sequence", "DMethodFlow.call", "DMethodFlowSeq.last",
   "DMethodFlowSeq.cons"]

def clinkEnabled (rule : String) : Bool :=
  match clinkProfile with
  | none => true
  | some rules => rules.contains rule

def clinkPolicyErrors (known : List String) (profile : Option (List String)) : List String :=
  match profile with
  | none => []
  | some rules =>
    (rules.filter (!known.contains ·)).map ("unknown clink: " ++ ·) ++
    (if rules.eraseDups == rules then [] else ["duplicate clinks in profile"])

end Ratchet
