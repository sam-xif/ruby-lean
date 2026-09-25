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
  | .int _ => ["InitJudge.intLit"]
  | .var .lvar _ => ["InitJudge.var"]
  | .vasgn .ivar _ e => "InitJudge.ivarAsgn" :: initRules e
  | .seq es => "InitJudge.seq" :: initSeqRules es
  | .super' es none => "InitJudge.superInit" :: initArgRules es
  | _ => ["?"]

def initSeqRules : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "InitJudgeSeq.last" :: initRules e
  | e :: e' :: es => "InitJudgeSeq.cons" :: (initRules e ++ initSeqRules (e' :: es))

def initArgRules : List Ratchet.Expr → List String
  | [] => ["InitJudgeAll.nil"]
  | e :: es => "InitJudgeAll.cons" :: (initRules e ++ initArgRules es)
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
def explicitSendRule (C : CTable) (Γ : Env) (recv : Ratchet.Expr) (name : String) : String :=
  if name == "new" then
    match recv with
    | .const cn => if noDeclaredSelectorB C cn "initialize" then "newDefault"
      else if inheritedSelectorB C cn "initialize" then "newInherited" else "newInst"
    | _ => "newInst"
  else match recv with
  | .const _ => "callSingleton"
  | .send (some (.const cn)) "new" _ none =>
    if inheritedSelectorB C cn name then "callInherited" else "callMethodSig"
  | .send _ "new" _ none => "callMethodSig"
  | .var .lvar x => match envGet? Γ x with
    | some (.inst cn _) => if inheritedSelectorB C cn name then "callInherited" else "callMethodSig"
    | _ => "prim"
  | _ => "prim"

mutual
def rulesUsedAt (C : CTable) (domains : List (String × Env)) (Γ : Env) : Ratchet.Expr → List String
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
  | .vasgn .lvar _ e => "vasgn" :: rulesUsedAt C domains Γ e
  | .vasgn .ivar _ e => "scalarIvarAsgn" :: rulesUsedAt C domains Γ e
  | .seq es => "seq" :: rulesUsedSeqAt C domains Γ es
  | .send (some r) name args none => explicitSendRule C Γ r name :: (rulesUsedAt C domains Γ r ++ rulesUsedArgsAt C domains Γ args)
  | .class' _ none body => "classDecl" :: classRulesAt C domains body
  | .class' _ (some super) body => "subclassDecl" :: (rulesUsedAt C domains Γ super ++ classRulesAt C domains body)
  | .def' name _ body => "defDecl" ::
    (if hasSelfCall name body then "recursive" :: scopedRules name body else
      rulesUsedAt C domains (((domains.find? (·.1 == name)).map (·.2)).getD []) body)
  | .send none "new" args none => "newImplicit" :: rulesUsedArgsAt C domains Γ args
  | .send none _ args none => "callSig" :: rulesUsedArgsAt C domains Γ args
  | .if' c t (some e) => "if'" :: (rulesUsedAt C domains Γ c ++ rulesUsedAt C domains Γ t ++ rulesUsedAt C domains Γ e)
  | .if' c t none => "ifNoElse" :: (rulesUsedAt C domains Γ c ++ rulesUsedAt C domains Γ t)
  | .array es => "arrayLit" :: rulesUsedArgsAt C domains Γ es
  | .hash ps => "hashLit" :: rulesUsedPairsAt C domains Γ ps
  | _ => ["?"]

def rulesUsedSeqAt (C : CTable) (domains : List (String × Env)) (Γ : Env) : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: rulesUsedAt C domains Γ e
  | e :: e' :: es => "DJudgeSeq.cons" :: (rulesUsedAt C domains Γ e ++ rulesUsedSeqAt C domains Γ (e' :: es))

def rulesUsedArgsAt (C : CTable) (domains : List (String × Env)) (Γ : Env) : List Ratchet.Expr → List String
  | [] => ["DJudgeAll.nil"]
  | e :: es => "DJudgeAll.cons" :: (rulesUsedAt C domains Γ e ++ rulesUsedArgsAt C domains Γ es)

def rulesUsedPairsAt (C : CTable) (domains : List (String × Env)) (Γ : Env) : List (Ratchet.Expr × Ratchet.Expr) → List String
  | [] => ["DJudgePairs.nil"]
  | (k, v) :: ps => "DJudgePairs.cons" :: (rulesUsedAt C domains Γ k ++ rulesUsedAt C domains Γ v ++ rulesUsedPairsAt C domains Γ ps)

def classRulesAt (C : CTable) (domains : List (String × Env)) : Ratchet.Expr → List String
  | .def' "initialize" _ body => "initDef" :: "InitJudge.ignoreResult" :: initRules body
  | .def' _ _ body => "memberDef" :: rulesUsedAt C domains [] body
  | .defs .self' _ _ body => "singletonDef" :: rulesUsedAt C domains [] body
  | .seq es => "seq" :: classSeqRulesAt C domains es
  | .nil => ["nilLit"]
  | _ => ["?"]

def classSeqRulesAt (C : CTable) (domains : List (String × Env)) : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: classRulesAt C domains e
  | e :: e' :: es => "DJudgeSeq.cons" :: (classRulesAt C domains e ++ classSeqRulesAt C domains (e' :: es))
end

def rulesUsed (e : Ratchet.Expr) : List String := rulesUsedAt (syntaxClasses e) [] [] e

def rulesUsedAll (es : List Ratchet.Expr) : List String := es.flatMap rulesUsed

/-- Return annotations are absent from the stripped AST. Record their extra conversion
rule independently of proof extraction; RuleAudit checks exact equality per rung. -/
def annotationRules : List (String × List String) :=
  [("073-class-factory-method", ["instanceType"])]

/-- Parameter annotations are also erased. Scope them to the top-level method name;
receiver domains distinguish instance dispatch from a primitive send on a local. -/
def annotationDomains : List (String × List (String × Env)) :=
  [("075-class-instance-as-fun-arg", [("describe", [("p", .inst "Point" (.ivarCons "@x" .int .ivar0))])])]

def rulesUsedFor (q : String × Ratchet.Expr) : List String :=
  let domains := ((annotationDomains.find? (·.1 == q.1)).map (·.2)).getD []
  rulesUsedAt (syntaxClasses q.2) domains [] q.2 ++ ((annotationRules.find? (·.1 == q.1)).map (·.2)).getD []

def rulesPredicted : List String := safeRungs.flatMap rulesUsedFor

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
