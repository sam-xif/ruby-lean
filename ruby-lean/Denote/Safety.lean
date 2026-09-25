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

/-- Erased annotations used only by the rule predictor, independently of proof extraction. -/
structure RuleAnnotations where
  params : List (String × Env) := []
  results : List ((String × String) × String) := []

/-- Follow receiver-producing syntax and declared result classes. This predicts a dispatch
rule; the checker separately requires exact initialized-instance evidence. -/
def receiverClass? (ann : RuleAnnotations) (Γ : Env) : Ratchet.Expr → Option String
  | .var .lvar x => match envGet? Γ x with
    | some (.inst cn _) => some cn
    | _ => none
  | .send (some (.const cn)) "new" _ none => some cn
  | .send (some recv) name _ none => do
    let cn ← receiverClass? ann Γ recv
    ((ann.results.find? (·.1 == (cn, name))).map (·.2))
  | _ => none

/-- Predict using declarations and scoped annotations, without fixed selector names. -/
def explicitSendRule (C : CTable) (ann : RuleAnnotations) (Γ : Env)
    (recv : Ratchet.Expr) (name : String) : String :=
  if name == "new" then
    match recv with
    | .const cn => if noDeclaredSelectorB C cn "initialize" then "newDefault"
      else if inheritedSelectorB C cn "initialize" then "newInherited" else "newInst"
    | _ => "newInst"
  else match recv with
  | .const _ => "callSingleton"
  | _ => match receiverClass? ann Γ recv with
    | some cn => if inheritedSelectorB C cn name then "callInherited" else "callMethodSig"
    | none => match recv with
      | .send _ "new" _ none => "callMethodSig"
      | _ => "prim"

mutual
def rulesUsedAt (C : CTable) (ann : RuleAnnotations) (Γ : Env) : Ratchet.Expr → List String
  | .int _ => ["intLit"]
  | .flt _ => ["fltLit"]
  | .str _ => ["strLit"]
  | .sym _ => ["symLit"]
  | .tru => ["truLit"]
  | .fls => ["flsLit"]
  | .nil => ["nilLit"]
  | .vcall "x" => ["bareName"]
  | .vcall _ => ["vcallMethodSig"]
  | .self' => ["selfRead"]
  | .var .lvar _ => ["var"]
  | .var .ivar _ => ["ivarRead"]
  | .const _ => ["constClass"]
  | .vasgn .lvar _ e => "vasgn" :: rulesUsedAt C ann Γ e
  | .vasgn .ivar _ e => "scalarIvarAsgn" :: rulesUsedAt C ann Γ e
  | .seq es => "seq" :: rulesUsedSeqAt C ann Γ es
  | .send (some r) name args none => explicitSendRule C ann Γ r name :: (rulesUsedAt C ann Γ r ++ rulesUsedArgsAt C ann Γ args)
  | .class' _ none body => "classDecl" :: classRulesAt C ann body
  | .module' _ body => "moduleDecl" :: classRulesAt C ann body
  | .class' _ (some super) body => "subclassDecl" :: (rulesUsedAt C ann Γ super ++ classRulesAt C ann body)
  | .def' name _ body => "defDecl" ::
    (if hasSelfCall name body then "recursive" :: scopedRules name body else
      rulesUsedAt C ann (((ann.params.find? (·.1 == name)).map (·.2)).getD []) body)
  | .send none "new" args none => "newImplicit" :: rulesUsedArgsAt C ann Γ args
  | .send none _ args none => "callSig" :: rulesUsedArgsAt C ann Γ args
  | .if' c t (some e) => "if'" :: (rulesUsedAt C ann Γ c ++ rulesUsedAt C ann Γ t ++ rulesUsedAt C ann Γ e)
  | .if' c t none => "ifNoElse" :: (rulesUsedAt C ann Γ c ++ rulesUsedAt C ann Γ t)
  | .array es => "arrayLit" :: rulesUsedArgsAt C ann Γ es
  | .hash ps => "hashLit" :: rulesUsedPairsAt C ann Γ ps
  | _ => ["?"]

def rulesUsedSeqAt (C : CTable) (ann : RuleAnnotations) (Γ : Env) : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: rulesUsedAt C ann Γ e
  | e :: e' :: es => "DJudgeSeq.cons" :: (rulesUsedAt C ann Γ e ++ rulesUsedSeqAt C ann Γ (e' :: es))

def rulesUsedArgsAt (C : CTable) (ann : RuleAnnotations) (Γ : Env) : List Ratchet.Expr → List String
  | [] => ["DJudgeAll.nil"]
  | e :: es => "DJudgeAll.cons" :: (rulesUsedAt C ann Γ e ++ rulesUsedArgsAt C ann Γ es)

def rulesUsedPairsAt (C : CTable) (ann : RuleAnnotations) (Γ : Env) : List (Ratchet.Expr × Ratchet.Expr) → List String
  | [] => ["DJudgePairs.nil"]
  | (k, v) :: ps => "DJudgePairs.cons" :: (rulesUsedAt C ann Γ k ++ rulesUsedAt C ann Γ v ++ rulesUsedPairsAt C ann Γ ps)

def classRulesAt (C : CTable) (ann : RuleAnnotations) : Ratchet.Expr → List String
  | .def' "initialize" _ body => "initDef" :: "InitJudge.ignoreResult" :: initRules body
  | .def' _ _ body => "memberDef" :: rulesUsedAt C ann [] body
  | .defs .self' _ _ body => "singletonDef" :: rulesUsedAt C ann [] body
  | .seq es => "seq" :: classSeqRulesAt C ann es
  | .nil => ["nilLit"]
  | _ => ["?"]

def classSeqRulesAt (C : CTable) (ann : RuleAnnotations) : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: classRulesAt C ann e
  | e :: e' :: es => "DJudgeSeq.cons" :: (classRulesAt C ann e ++ classSeqRulesAt C ann (e' :: es))
end

def rulesUsed (e : Ratchet.Expr) : List String := rulesUsedAt (syntaxClasses e) {} [] e

def rulesUsedAll (es : List Ratchet.Expr) : List String := es.flatMap rulesUsed

/-- Return annotations are absent from the stripped AST. Record their extra conversion
rule independently of proof extraction; RuleAudit checks exact equality per rung. -/
def annotationRules : List (String × List String) :=
  [("073-class-factory-method", ["instanceType"]),
   ("076-class-self-returning-method", ["instanceType"])]

/-- Parameter and result annotations are erased. Record them by method/owner rather
than injecting rule names; RuleAudit compares the resulting prediction with the proof. -/
def annotationHints : List (String × RuleAnnotations) :=
  [("075-class-instance-as-fun-arg", { params :=
      [("describe", [("p", .inst "Point" (.ivarCons "@x" .int .ivar0))])] }),
   ("076-class-self-returning-method", { results := [(("Point", "myself"), "Point")] })]

def rulesUsedFor (q : String × Ratchet.Expr) : List String :=
  let ann := ((annotationHints.find? (·.1 == q.1)).map (·.2)).getD {}
  rulesUsedAt (syntaxClasses q.2) ann [] q.2 ++ ((annotationRules.find? (·.1 == q.1)).map (·.2)).getD []

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
