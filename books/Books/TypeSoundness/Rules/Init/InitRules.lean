import Books.TypeSoundness.Rules.Init.InitWrite
import Books.TypeSoundness.Rules.Init.InitBranch

/-! Constructor-mirroring forms for the initializer families (super: SuperInitRules). -/
namespace Checker.Soundness.Typed

abbrev SemSafeCtxA.InitJudge.intLit := @SemInitA.intLit
abbrev SemSafeCtxA.InitJudge.var := @SemInitA.var
abbrev SemSafeCtxA.InitJudge.ivarAsgn := @SemInitA.ivarAsgnChecked
abbrev SemSafeCtxA.InitJudge.seq := @SemInitA.sequence
abbrev SemSafeCtxA.InitJudge.ignoreResult := @SemInitA.ignoreResult
abbrev SemSafeCtxA.InitJudge.strLit := @SemInitA.strLit
abbrev SemSafeCtxA.InitJudge.widenL := @SemInitA.widenL
abbrev SemSafeCtxA.InitJudge.widenR := @SemInitA.widenR
abbrev SemSafeCtxA.InitJudge.ifVar := @SemInitA.ifVar
abbrev SemSafeCtxA.InitJudgeSeq.last := @SemInitSeqA.last
abbrev SemSafeCtxA.InitJudgeSeq.cons := @SemInitSeqA.cons

end Checker.Soundness.Typed
