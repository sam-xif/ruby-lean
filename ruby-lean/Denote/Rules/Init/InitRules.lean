import Denote.Rules.Init.InitWrite
import Denote.Rules.Super.SuperExpr

/-! Constructor-mirroring forms for the three initializer families. -/
namespace Ratchet.Denote.Typed

abbrev SemSafeCtxA.InitJudge.intLit := @SemInitA.intLit
abbrev SemSafeCtxA.InitJudge.var := @SemInitA.var
abbrev SemSafeCtxA.InitJudge.ivarAsgn := @SemInitA.ivarAsgnChecked
abbrev SemSafeCtxA.InitJudge.seq := @SemInitA.sequence
abbrev SemSafeCtxA.InitJudge.ignoreResult := @SemInitA.ignoreResult
abbrev SemSafeCtxA.InitJudge.superInit := @SemInitA.superInit
abbrev SemSafeCtxA.InitJudgeSeq.last := @SemInitSeqA.last
abbrev SemSafeCtxA.InitJudgeSeq.cons := @SemInitSeqA.cons
abbrev SemSafeCtxA.InitJudgeAll.nil := @SemInitAllA.nil
abbrev SemSafeCtxA.InitJudgeAll.cons := @SemInitAllA.cons

end Ratchet.Denote.Typed
