import Denote.Sem.Core.Boot

/-! An ordinary definition must have a writable Object method table. The frozen
error path runs callbacks not described by the ordinary-method judgment. -/
namespace Ratchet.Denote
open RubyCore

private def frozenForged : Machine :=
  let h := bootMachine.heap.set Boot.objectId
    { bootMachine.heap.get Boot.objectId with frozen := true }
  let md : MethodDef :=
    { params := [.req "message"], owner := Boot.frozenErrorId, fromPrelude := true,
      body := .send (some .nil) "+" [.int 1] .none }
  { bootMachine with heap := defineMethod h Boot.frozenErrorId "initialize" md }

-- The complete former state check, retaining its old runtime-main requirement.
private def legacyBootStateB (m : Machine) : Bool :=
  saturatedB m.heap && coreOkB m.heap && frameOkB m &&
  topScopeB m && methodsExactB Ratchet.ctx0 m &&
  nameFreeB m && missFreeB m && selfLiveB m &&
  localsEmptyB m && queryOkB m && clsQueryOkB m &&
  baseChainsOkB m && nilQueryOkB m &&
  primitiveDispatchB m.heap (nameFreeN Ratchet.ctx0) &&
  primitiveErrorsB m.heap && stringPayloadB m.heap &&
  arrayPayloadB m.heap && hashPayloadB m.heap && mainReadyBaseB m &&
  newDispatchB m.heap (classOf m.heap (.ref Boot.objectId)) &&
  globalConstsOkB Ratchet.ctx0.pos.globalConsts m.heap &&
  moduleBaseB (nameFreeN Ratchet.ctx0) m.heap && Proof.namesOkB m.heap &&
  m.currentFrame.localAlias.isNone && rootCleanB m && primitiveInitB m.heap &&
  rootInitOkB Ratchet.ctx0.defs m.heap

#guard legacyBootStateB frozenForged
#guard !bootStateB frozenForged
#guard Semantics.typeStuck (Interp.run 400
  { frozenForged with ctl := .eval (.def' "bump" [] (.int 1)) })
#guard mainReadyB bootMachine

#print axioms MainReady.writable
end Ratchet.Denote
