import Books.TypeSoundness.Rules.Method.MethodDispatch
import Books.TypeSoundness.Conformance.Core.Boot

/-! User phase alone does not exclude a library-origin source definition. -/
namespace Checker.Soundness.Typed
open RubyCore Checker.Soundness

private def libraryRoot : Machine :=
  let frames := bootMachine.frames.set! (bootMachine.stack.headD 0)
    { bootMachine.currentFrame with libraryOrigin := true }
  { bootMachine with frames }

private def legacyReadyB (m : Machine) : Bool :=
  mainReadyBaseB m &&
    decide ((m.heap.classPayload? Boot.objectId).bind (·.attached) = none) &&
    !(m.heap.get Boot.objectId).frozen

private def legacyBootStateB (m : Machine) : Bool :=
  saturatedB m.heap && coreOkB m.heap && frameOkB m &&
  topScopeB m && methodsExactB Checker.ctx0 m &&
  nameFreeB m && missFreeB m && selfLiveB m &&
  localsEmptyB m && queryOkB m && clsQueryOkB m &&
  baseChainsOkB m && nilQueryOkB m &&
  primitiveDispatchB m.heap (nameFreeN Checker.ctx0) &&
  primitiveErrorsB m.heap && stringPayloadB m.heap &&
  arrayPayloadB m.heap && hashPayloadB m.heap && legacyReadyB m &&
  newDispatchB m.heap (classOf m.heap (.ref Boot.objectId)) &&
  globalConstsOkB Checker.ctx0.pos.globalConsts m.heap &&
  moduleBaseB (nameFreeN Checker.ctx0) m.heap && Proof.namesOkB m.heap &&
  m.currentFrame.localAlias.isNone && rootCleanB m && primitiveInitB m.heap &&
  rootInitOkB Checker.ctx0.defs m.heap

#guard legacyBootStateB libraryRoot
#guard !bootStateB libraryRoot
#guard (definedMethod libraryRoot "bump" [] (.int 1)).fromPrelude
#guard !ordinaryMethodCodeB Boot.objectId [] (definedMethod libraryRoot "bump" [] (.int 1))
#guard mainReadyB bootMachine
end Checker.Soundness.Typed
