import Books.TypeSoundness.Rules.Init.InitRules
import Books.TypeSoundness.Rules.Super.SuperExpr

/-! Initializer rules that run a superclass initializer. -/
namespace Checker.Soundness.Typed

abbrev SemSafeCtxA.InitJudge.superInit := @SemInitA.superInit
abbrev SemSafeCtxA.InitJudgeAll.nil := @SemInitAllA.nil
abbrev SemSafeCtxA.InitJudgeAll.cons := @SemInitAllA.cons

end Checker.Soundness.Typed
