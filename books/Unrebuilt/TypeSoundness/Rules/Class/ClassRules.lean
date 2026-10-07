import Books.TypeSoundness.Rules.Class.ClassHeaderRun
import Books.TypeSoundness.Rules.Instance.MemberDefine
import Books.TypeSoundness.Rules.Constructor.ConstructorExpr
import Books.TypeSoundness.Rules.Instance.InstanceImplicit
import Books.TypeSoundness.Conformance.Class.ClassGuards
import Books.TypeSoundness.Conformance.Names.NativeGuards

/-! Constructor-ready semantic forms: every side condition is syntax/type data or a
proved body premise. No heap predicate, fixed class name, or signature-only admission is
left for the checker to supply. These are the interfaces for the forthcoming DJudge rules. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

-- SemSafeCtxA.classDecl now lives in ClassDeclActual (actual registration heap).

-- SemSafeCtxA.memberDef now lives in MemberDefActual.

-- SemSafeCtxA.initDef/newInst now live in Constructor/NewInstActual.

-- SemSafeCtxA.callMethodSig now lives in CallMethodSigActual.

-- SemSafeCtxA.vcallMethodSig now lives in VcallMethodSigActual.

#print axioms SemSafeCtxA.classDecl
#print axioms SemSafeCtxA.memberDef
#print axioms SemSafeCtxA.callMethodSig
end Checker.Soundness.Typed
