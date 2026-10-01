import Denote.Sem.Core.Boot
import Ratchet.Check.Check

/-! The former allocator capability omitted native construction metadata. -/
namespace Ratchet.Denote.Typed
open RubyCore Ratchet.Denote

private def withObject (f : ClassPayload → ClassPayload) : Machine :=
  let cp := (bootMachine.heap.classPayload? Boot.objectId).getD { superclass := none, name := "" }
  { bootMachine with heap := bootMachine.heap.setClassPayload Boot.objectId (f cp) }
private def unavailable := withObject fun cp => { cp with allocatorUnavailable := true }
private def uninitialized := withObject fun cp => { cp with initialized := false }
private def attached := withObject fun cp => { cp with attached := some Boot.mainId }
private def ancestryMissing := withObject fun cp => { cp with ancestryReady := false }

private def legacyReadyB (m : Machine) : Bool :=
  mainReadyBaseB m &&
    decide ((m.heap.classPayload? Boot.objectId).bind (·.attached) = none) &&
    !(m.heap.get Boot.objectId).frozen && !m.currentFrame.libraryOrigin &&
    mainOwnNamesB m.heap && classHooksQuietB m.heap

private def legacyBootStateBaseB (m : Machine) : Bool :=
  saturatedB m.heap && coreOkB m.heap && frameOkB m &&
  topScopeB m && methodsExactB Ratchet.ctx0 m &&
  nameFreeB m && missFreeB m && selfLiveB m &&
  localsEmptyB m && queryOkB m && clsQueryOkB m
    && baseChainsOkB m && nilQueryOkB m
    && primitiveDispatchB m.heap (nameFreeN Ratchet.ctx0)
    && primitiveErrorsB m.heap && stringPayloadB m.heap
    && arrayPayloadB m.heap
    && hashPayloadB m.heap && legacyReadyB m
    && newDispatchB m.heap (classOf m.heap (.ref Boot.objectId))
    && globalConstsOkB Ratchet.ctx0.pos.globalConsts m.heap
    && moduleBaseB (nameFreeN Ratchet.ctx0) m.heap
    && Proof.namesOkB m.heap
    && m.currentFrame.localAlias.isNone
    && rootCleanB m
    && primitiveInitB m.heap

private def legacyBootStateB (m : Machine) : Bool :=
  legacyBootStateBaseB m && rootInitOkB Ratchet.ctx0.defs m.heap

private def legacyPlainB (h : Heap) (k : ObjId) : Bool :=
  decide (k < h.objs.size) && k != Boot.classId && k != Boot.moduleId &&
  k != Boot.mathId && k != Boot.stringId &&
  (h.classPayload? k).map (·.isModule) == some false &&
  (ancestors h k).contains Boot.basicObjectId && (Builtins.allocatableCore h k).isNone &&
  !(ancestors h k).any (fun a => Builtins.payloadCoreClasses.contains a || a == Boot.exceptionId)

#guard legacyBootStateB unavailable
#guard !bootStateB unavailable
#guard !bootStateB ancestryMissing
#guard objectClassFlagsB bootMachine.heap
#guard plainAllocationReadyB bootMachine.heap Boot.objectId
#guard [unavailable, uninitialized, attached].all fun m =>
  legacyPlainB m.heap Boot.objectId && !plainAllocationReadyB m.heap Boot.objectId &&
    match Interp.callConstruct m (.ref Boot.objectId) [] none [] with
    | .next n => Semantics.typeStuck (Interp.run 100 n)
    | _ => false
#guard !plainAllocationReadyB ancestryMissing.heap Boot.objectId
#guard Ratchet.validateDWith (fun _ => true)
  (.seq [.class' "FreshAllocatorWitness" none (.int 1),
    .send (some (.const "FreshAllocatorWitness")) "new" [] none])
  (.seq [.classDecl "FreshAllocatorWitness" none (.intLit 1),
    .newInst "FreshAllocatorWitness" [] (.inst "FreshAllocatorWitness" .ivar0)])
#guard Semantics.typeStuck (Interp.run 100
  { unavailable with ctl := .eval (.seq [.class' "FreshAllocatorWitness" none (.int 1),
    .send (some (.const "FreshAllocatorWitness")) "new" [] .none]), kont := [] })
end Ratchet.Denote.Typed
