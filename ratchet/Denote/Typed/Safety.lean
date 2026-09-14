import Denote.Typed.CorpusSafety
import Denote.Typed.MethodInstallControls
import Denote.Typed.MethodRuleControls

/-! Safety coverage: predict rules from syntax, then cross-check against the actual proof
terms in `RuleAudit`. Concrete programs and their safety theorems live in `CorpusSafety`.
The list companions count as rules too: their premises cross the same family boundary. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

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
