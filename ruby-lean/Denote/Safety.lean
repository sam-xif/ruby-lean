import Denote.Examples.CorpusSafety

/-! Safety coverage: predict rules from syntax, then cross-check against the actual proof
terms in `RuleAudit`. Concrete programs and their safety theorems live in `CorpusSafety`.
The list companions count as rules too: their premises cross the same family boundary. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/- The closed-subtree predictor is separate so scoped `embed` does not claim recursive
rules. Both predictions are checked against the worked proof terms, never trusted. -/
mutual
def plainRules : Ratchet.Expr → List String
  | .int _ => ["intLit"]
  | .flt _ => ["fltLit"]
  | .str _ => ["strLit"]
  | .sym _ => ["symLit"]
  | .tru => ["truLit"]
  | .fls => ["flsLit"]
  | .nil => ["nilLit"]
  | .vcall "x" => ["bareName"]
  | .var .lvar _ => ["var"]
  | .vasgn .lvar _ e => "vasgn" :: plainRules e
  | .seq es => "seq" :: plainRulesSeq es
  | .send (some r) _ args none => "prim" :: (plainRules r ++ plainRulesArgs args)
  | .def' _ _ body => "defDecl" :: plainRules body
  | .send none _ args none => "callSig" :: plainRulesArgs args
  | .if' c t (some e) => "if'" :: (plainRules c ++ plainRules t ++ plainRules e)
  | .if' c t none => "ifNoElse" :: (plainRules c ++ plainRules t)
  | .array es => "arrayLit" :: plainRulesArgs es
  | .hash ps => "hashLit" :: plainRulesPairs ps
  | _ => ["?"]

def plainRulesSeq : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: plainRules e
  | e :: e' :: es => "DJudgeSeq.cons" :: (plainRules e ++ plainRulesSeq (e' :: es))

def plainRulesArgs : List Ratchet.Expr → List String
  | [] => ["DJudgeAll.nil"]
  | e :: es => "DJudgeAll.cons" :: (plainRules e ++ plainRulesArgs es)

def plainRulesPairs : List (Ratchet.Expr × Ratchet.Expr) → List String
  | [] => ["DJudgePairs.nil"]
  | (k, v) :: ps => "DJudgePairs.cons" :: (plainRules k ++ plainRules v ++ plainRulesPairs ps)
end

mutual
def hasSelfCall (name : String) : Ratchet.Expr → Bool
  | .send recv m args none =>
    (recv.isNone && m == name) || selfCallOpt name recv || selfCallList name args
  | .if' c t e => hasSelfCall name c || hasSelfCall name t || selfCallOpt name e
  | .vasgn _ _ e => hasSelfCall name e
  | .seq es | .array es => selfCallList name es
  | .hash ps => selfCallPairs name ps
  | _ => false

def selfCallOpt (name : String) : Option Ratchet.Expr → Bool
  | none => false
  | some e => hasSelfCall name e

def selfCallList (name : String) : List Ratchet.Expr → Bool
  | [] => false
  | e :: es => hasSelfCall name e || selfCallList name es

def selfCallPairs (name : String) : List (Ratchet.Expr × Ratchet.Expr) → Bool
  | [] => false
  | (k, v) :: ps => hasSelfCall name k || hasSelfCall name v || selfCallPairs name ps
end

mutual
def scopedRules (name : String) (e : Ratchet.Expr) : List String :=
  if !hasSelfCall name e then "DJudgeRec.embed" :: plainRules e else
  match e with
  | .send (some r) _ args none =>
    "DJudgeRec.prim" :: (scopedRules name r ++ scopedArgRules name args)
  | .send none m args none =>
    if m == name then "DJudgeRec.selfCall" :: scopedArgRules name args else ["?"]
  | .if' c t (some el) =>
    "DJudgeRec.if'" :: (scopedRules name c ++ scopedRules name t ++ scopedRules name el)
  | _ => ["?"]

def scopedArgRules (name : String) : List Ratchet.Expr → List String
  | [] => ["DJudgeRecAll.nil"]
  | e :: es => "DJudgeRecAll.cons" :: (scopedRules name e ++ scopedArgRules name es)
end

/-! Prediction for the currently worked initializer syntax. A void annotation adds
ignoreResult at the definition; RuleAudit independently checks this against the proof. -/
mutual
def initRules : Ratchet.Expr → List String
  | .var .lvar _ => ["InitJudge.var"]
  | .vasgn .ivar _ e => "InitJudge.ivarAsgn" :: initRules e
  | .seq es => "InitJudge.seq" :: initSeqRules es
  | _ => ["?"]

def initSeqRules : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "InitJudgeSeq.last" :: initRules e
  | e :: e' :: es => "InitJudgeSeq.cons" :: (initRules e ++ initSeqRules (e' :: es))
end

/-! Syntax-only class summary for predicting own versus inherited dispatch. It is not a
typing premise: RuleAudit still checks every prediction against the actual proof term.
Reopening and indirect receivers will need a richer predictor when they gain worked proofs. -/
mutual
def syntaxMethods : Ratchet.Expr → List Defn
  | .def' name ps body => [⟨name, ps, body⟩]
  | .seq es => syntaxMethodList es
  | _ => []
def syntaxMethodList : List Ratchet.Expr → List Defn
  | [] => []
  | e :: es => syntaxMethods e ++ syntaxMethodList es
end

mutual
def syntaxClasses : Ratchet.Expr → CTable
  | .class' name super body =>
    [{ classHeader name with methods := syntaxMethods body, super? :=
      match super with | some (.const parent) => some parent | _ => none }]
  | .seq es => syntaxClassList es
  | _ => []
def syntaxClassList : List Ratchet.Expr → CTable
  | [] => []
  | e :: es => syntaxClasses e ++ syntaxClassList es
end

def inheritedSelectorB (C : CTable) (cn name : String) : Bool :=
  ((ancestors? C cn).bind fun ns => searchMro C ns name).any (fun (owner, _) => owner != cn)

/-- Predict using the extracted declarations, without any fixed class or method name. -/
def explicitSendRule (C : CTable) (recv : Ratchet.Expr) (name : String) : String :=
  if name == "new" then
    match recv with
    | .const cn => if inheritedSelectorB C cn "initialize" then "newInherited" else "newInst"
    | _ => "newInst"
  else match recv with
  | .send (some (.const cn)) "new" _ none =>
    if inheritedSelectorB C cn name then "callInherited" else "callMethodSig"
  | .send _ "new" _ none => "callMethodSig"
  | _ => "prim"

mutual
def rulesUsedAt (C : CTable) : Ratchet.Expr → List String
  | .int _ => ["intLit"]
  | .flt _ => ["fltLit"]
  | .str _ => ["strLit"]
  | .sym _ => ["symLit"]
  | .tru => ["truLit"]
  | .fls => ["flsLit"]
  | .nil => ["nilLit"]
  | .vcall "x" => ["bareName"]
  | .vcall _ => ["vcallMethodSig"]
  | .var .lvar _ => ["var"]
  | .var .ivar _ => ["ivarRead"]
  | .const _ => ["constClass"]
  | .vasgn .lvar _ e => "vasgn" :: rulesUsedAt C e
  | .seq es => "seq" :: rulesUsedSeqAt C es
  | .send (some r) name args none => explicitSendRule C r name :: (rulesUsedAt C r ++ rulesUsedArgsAt C args)
  | .class' _ none body => "classDecl" :: classRulesAt C body
  | .class' _ (some super) body => "subclassDecl" :: (rulesUsedAt C super ++ classRulesAt C body)
  | .def' name _ body => "defDecl" ::
    (if hasSelfCall name body then "recursive" :: scopedRules name body else rulesUsedAt C body)
  | .send none _ args none => "callSig" :: rulesUsedArgsAt C args
  | .if' c t (some e) => "if'" :: (rulesUsedAt C c ++ rulesUsedAt C t ++ rulesUsedAt C e)
  | .if' c t none => "ifNoElse" :: (rulesUsedAt C c ++ rulesUsedAt C t)
  | .array es => "arrayLit" :: rulesUsedArgsAt C es
  | .hash ps => "hashLit" :: rulesUsedPairsAt C ps
  | _ => ["?"]

def rulesUsedSeqAt (C : CTable) : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: rulesUsedAt C e
  | e :: e' :: es => "DJudgeSeq.cons" :: (rulesUsedAt C e ++ rulesUsedSeqAt C (e' :: es))

def rulesUsedArgsAt (C : CTable) : List Ratchet.Expr → List String
  | [] => ["DJudgeAll.nil"]
  | e :: es => "DJudgeAll.cons" :: (rulesUsedAt C e ++ rulesUsedArgsAt C es)

def rulesUsedPairsAt (C : CTable) : List (Ratchet.Expr × Ratchet.Expr) → List String
  | [] => ["DJudgePairs.nil"]
  | (k, v) :: ps => "DJudgePairs.cons" :: (rulesUsedAt C k ++ rulesUsedAt C v ++ rulesUsedPairsAt C ps)

def classRulesAt (C : CTable) : Ratchet.Expr → List String
  | .def' "initialize" _ body => "initDef" :: "InitJudge.ignoreResult" :: initRules body
  | .def' _ _ body => "memberDef" :: rulesUsedAt C body
  | .seq es => "seq" :: classSeqRulesAt C es
  | .nil => ["nilLit"]
  | _ => ["?"]

def classSeqRulesAt (C : CTable) : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: classRulesAt C e
  | e :: e' :: es => "DJudgeSeq.cons" :: (classRulesAt C e ++ classSeqRulesAt C (e' :: es))
end

def rulesUsed (e : Ratchet.Expr) : List String := rulesUsedAt (syntaxClasses e) e

def rulesUsedAll (es : List Ratchet.Expr) : List String := es.flatMap rulesUsed

def rulesPredicted : List String := rulesUsedAll (safeRungs.map (·.2))

/-- All registered rules now occur in corpus safety proofs. The ceiling only decreases. -/
def unexercised : List String := []
def unexercisedCeiling : Nat := 0

#guard unexercised.length ≤ unexercisedCeiling
#guard dRegisteredRules.all (fun r => rulesPredicted.contains r || unexercised.contains r)
#guard unexercised.all (fun r => dRegisteredRules.contains r && !rulesPredicted.contains r)
#guard dUnregisteredRules.all (fun r => !rulesPredicted.contains r)
#guard !rulesPredicted.contains "?"

#print axioms safeRungs_safe
end Ratchet.Denote.Typed
