import Denote.Judgment.FlowRulesCore
import Denote.Rules.Iterator.FlowEach
import Denote.Rules.Iterator.FlowMap

/-! Registry names for the iterator flow contracts; the rest are in FlowRulesCore. -/
namespace Ratchet.Denote.Typed

abbrev SemSafeCtxA.DFlow.each := @SemFlow.each
abbrev SemSafeCtxA.DFlow.map := @SemFlow.map

end Ratchet.Denote.Typed
