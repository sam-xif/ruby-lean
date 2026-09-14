import Denote.Typed.CorpusSafety
import Denote.Typed.MethodInstallControls
import Denote.Typed.MethodRuleControls
import Denote.Typed.BoundedControls
import Denote.Typed.InstanceControls
import Denote.Typed.InitControls
import Denote.Typed.InitBodyControls
import Denote.Typed.ClassControls

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

mutual
def rulesUsed : Ratchet.Expr → List String
  | .int _ => ["intLit"]
  | .flt _ => ["fltLit"]
  | .str _ => ["strLit"]
  | .sym _ => ["symLit"]
  | .tru => ["truLit"]
  | .fls => ["flsLit"]
  | .nil => ["nilLit"]
  | .vcall "x" => ["bareName"]
  | .var .lvar _ => ["var"]
  | .vasgn .lvar _ e => "vasgn" :: rulesUsed e
  | .seq es => "seq" :: rulesUsedSeq es
  | .send (some r) _ args none => "prim" :: (rulesUsed r ++ rulesUsedArgs args)
  | .def' name _ body => "defDecl" ::
    (if hasSelfCall name body then "recursive" :: scopedRules name body else rulesUsed body)
  | .send none _ args none => "callSig" :: rulesUsedArgs args
  | .if' c t (some e) => "if'" :: (rulesUsed c ++ rulesUsed t ++ rulesUsed e)
  | .if' c t none => "ifNoElse" :: (rulesUsed c ++ rulesUsed t)
  | .array es => "arrayLit" :: rulesUsedArgs es
  | .hash ps => "hashLit" :: rulesUsedPairs ps
  | _ => ["?"]

def rulesUsedSeq : List Ratchet.Expr → List String
  | [] => ["?"]
  | [e] => "DJudgeSeq.last" :: rulesUsed e
  | e :: e' :: es => "DJudgeSeq.cons" :: (rulesUsed e ++ rulesUsedSeq (e' :: es))

def rulesUsedArgs : List Ratchet.Expr → List String
  | [] => ["DJudgeAll.nil"]
  | e :: es => "DJudgeAll.cons" :: (rulesUsed e ++ rulesUsedArgs es)

def rulesUsedPairs : List (Ratchet.Expr × Ratchet.Expr) → List String
  | [] => ["DJudgePairs.nil"]
  | (k, v) :: ps => "DJudgePairs.cons" :: (rulesUsed k ++ rulesUsed v ++ rulesUsedPairs ps)
end

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
