import Books.TypeSoundness.Judgment.FlowRulesCore
import Books.TypeSoundness.Rules.Iterator.FlowEach
import Books.TypeSoundness.Rules.Iterator.FlowMap

/-! Registry names for the iterator flow contracts; the rest are in FlowRulesCore. -/
namespace Checker.Soundness.Typed

abbrev SemSafeCtxA.DFlow.each := @SemFlow.each
abbrev SemSafeCtxA.DFlow.map := @SemFlow.map

end Checker.Soundness.Typed
