import Denote.Rules.Init.InitWrite

/-! Constructor-mirroring forms for the initializer families (super: SuperInitRules). -/
namespace Ratchet.Denote.Typed

abbrev SemSafeCtxA.InitJudge.intLit := @SemInitA.intLit
abbrev SemSafeCtxA.InitJudge.var := @SemInitA.var
abbrev SemSafeCtxA.InitJudge.ivarAsgn := @SemInitA.ivarAsgnChecked
abbrev SemSafeCtxA.InitJudge.seq := @SemInitA.sequence
abbrev SemSafeCtxA.InitJudge.ignoreResult := @SemInitA.ignoreResult
abbrev SemSafeCtxA.InitJudgeSeq.last := @SemInitSeqA.last
abbrev SemSafeCtxA.InitJudgeSeq.cons := @SemInitSeqA.cons

end Ratchet.Denote.Typed
