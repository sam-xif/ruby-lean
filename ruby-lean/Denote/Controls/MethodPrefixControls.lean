import Denote.Rules.Method.MethodDefine
import Denote.Sem.Core.Boot
import Ratchet.Check.Check
/-! A native method in main's singleton prefix wins ahead of a checked Object
definition. The former full state guard must accept this witness, the repair reject it. -/
namespace Ratchet.Denote.Typed
open RubyCore Ratchet.Denote
private def shadowMain : Machine :=
  let k := classOf bootMachine.heap (.ref Boot.mainId)
  let md : MethodDef :=
    { params := [], body := .nil, owner := k, builtin := some "Module#method_added" }
  { bootMachine with heap := defineMethod bootMachine.heap k "bump" md }

private def legacyReadyB (m : Machine) : Bool :=
  mainReadyBaseB m &&
    decide ((m.heap.classPayload? Boot.objectId).bind (·.attached) = none) &&
    !(m.heap.get Boot.objectId).frozen && !m.currentFrame.libraryOrigin

private def legacyBootStateB (m : Machine) : Bool :=
  saturatedB m.heap && coreOkB m.heap && frameOkB m &&
  topScopeB m && methodsExactB Ratchet.ctx0 m &&
  nameFreeB m && missFreeB m && selfLiveB m &&
  localsEmptyB m && queryOkB m && clsQueryOkB m &&
  baseChainsOkB m && nilQueryOkB m &&
  primitiveDispatchB m.heap (nameFreeN Ratchet.ctx0) &&
  primitiveErrorsB m.heap && stringPayloadB m.heap &&
  arrayPayloadB m.heap && hashPayloadB m.heap && legacyReadyB m &&
  newDispatchB m.heap (classOf m.heap (.ref Boot.objectId)) &&
  globalConstsOkB Ratchet.ctx0.pos.globalConsts m.heap &&
  moduleBaseB (nameFreeN Ratchet.ctx0) m.heap && Proof.namesOkB m.heap &&
  m.currentFrame.localAlias.isNone && rootCleanB m && primitiveInitB m.heap &&
  rootInitOkB Ratchet.ctx0.defs m.heap

#guard legacyBootStateB shadowMain
#guard !bootStateB shadowMain
#guard mainOwnNamesB bootMachine.heap
#guard Semantics.typeStuck (Interp.run 100
  { shadowMain with ctl := .eval (.seq [.def' "bump" [] (.int 1),
      .send none "bump" [] .none]), kont := [] })
#guard Ratchet.validateDWith (fun _ => true)
  (.seq [.def' "bump" [] (.int 1), .send none "bump" [] none])
  (.seq [.defDecl "bump" [] .int (.intLit 1), .callSig "bump" [] .int])
end Ratchet.Denote.Typed
