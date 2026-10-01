import Denote.Rules.Init.InitRules
import Denote.Rules.Super.SuperExpr

/-! Initializer rules that run a superclass initializer. -/
namespace Ratchet.Denote.Typed

abbrev SemSafeCtxA.InitJudge.superInit := @SemInitA.superInit
abbrev SemSafeCtxA.InitJudgeAll.nil := @SemInitAllA.nil
abbrev SemSafeCtxA.InitJudgeAll.cons := @SemInitAllA.cons

end Ratchet.Denote.Typed
