/-! Source-controlled clink admission during semantic rebuilding. Names are the
constructor suffixes reported by the registry, not chronological clink numbers.
`none` enables the complete authoring family; `some [...]` is an exact allowlist.
Shared by the isolated checker and the semantic registry.
Denote/Clink/ActiveProofs.lean imports the selected semantic proofs. -/
namespace Ratchet

def clinkProfileName : String := "semantic-rebuild"

def clinkProfile : Option (List String) := some
  ["intLit", "fltLit", "strLit", "symLit", "truLit", "flsLit", "nilLit",
   "seq", "DJudgeSeq.last", "DJudgeSeq.cons", "var", "vasgn",
   "prim", "DJudgeAll.nil", "DJudgeAll.cons", "if'", "ifNoElse", "bareName",
   "arrayLit", "hashLit", "DJudgePairs.nil", "DJudgePairs.cons", "defDecl", "callSig",
   "recursive", "DJudgeRec.embed", "DJudgeRec.prim", "DJudgeRec.if'", "DJudgeRec.selfCall",
   "DJudgeRecAll.nil", "DJudgeRecAll.cons", "classDecl", "constClass", "memberDef", "newDefault", "callMethodSig"]

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
