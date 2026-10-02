import Denote.Rules.Class.ClassHeaderRun
import Denote.Rules.Instance.MemberDefine
import Denote.Rules.Constructor.ConstructorExpr
import Denote.Rules.Instance.InstanceImplicit
import Denote.Sem.Class.ClassGuards
import Denote.Sem.Names.NativeGuards

/-! Constructor-ready semantic forms: every side condition is syntax/type data or a
proved body premise. No heap predicate, fixed class name, or signature-only admission is
left for the checker to supply. These are the interfaces for the forthcoming DJudge rules. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

-- SemSafeCtxA.classDecl now lives in ClassDeclActual (actual registration heap).

-- SemSafeCtxA.memberDef now lives in MemberDefActual.

-- SemSafeCtxA.initDef/newInst now live in Constructor/NewInstActual.

-- SemSafeCtxA.callMethodSig now lives in CallMethodSigActual.

-- SemSafeCtxA.vcallMethodSig now lives in VcallMethodSigActual.

#print axioms SemSafeCtxA.classDecl
#print axioms SemSafeCtxA.memberDef
#print axioms SemSafeCtxA.callMethodSig
end Ratchet.Denote.Typed
