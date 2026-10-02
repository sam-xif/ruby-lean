import Denote.Rules.Closure.FlowExpr
import Denote.Rules.Closure.FlowCall
import Denote.Rules.Closure.FlowSequence
import Denote.Rules.Closure.RequiredFlowCall

/-! Registry names for the non-iterator flow contracts (literal, locals, sequence,
stored-lambda calls). Iterator providers live in FlowRules. -/
namespace Ratchet.Denote.Typed

abbrev SemSafeCtxA.flow := @SemFlow.erase
abbrev SemSafeCtxA.DFlow.embed := @SemFlow.embed
abbrev SemSafeCtxA.DFlow.intLit := @SemFlow.intLit
abbrev SemSafeCtxA.DFlow.nilLit := @SemFlow.nilLit
abbrev SemSafeCtxA.DFlow.var := @SemFlow.var
abbrev SemSafeCtxA.DFlow.closureLiteral := @SemFlow.closureLiteral
abbrev SemSafeCtxA.DFlow.vasgn := @SemFlow.vasgn
abbrev SemSafeCtxA.DFlow.sequence := @SemFlow.sequence
abbrev SemSafeCtxA.DFlow.call := @SemFlow.call
abbrev SemSafeCtxA.DFlow.requiredCall := @SemFlow.requiredCall
abbrev SemSafeCtxA.DFlowSeq.last := @SemFlowSeq.last
abbrev SemSafeCtxA.DFlowSeq.cons := @SemFlowSeq.cons
abbrev SemSafeCtxA.DFlowAll.nil := @SemFlowAll.nil
abbrev SemSafeCtxA.DFlowAll.cons := @SemFlowAll.cons

end Ratchet.Denote.Typed
