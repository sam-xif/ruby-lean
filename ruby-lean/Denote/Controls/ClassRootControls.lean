import Denote.Rules.Class.ClassRun
import Denote.Sem.Class.ClassShape
import Denote.Sem.Core.Boot

/-! Main can have the expected chain while Object itself does not. Ordinary fresh classes
inherit the latter. The injected heap below passed the complete previous boot check. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def rootDetour : Machine :=
  { bootMachine with heap := { bootMachine.heap with objs := bootMachine.heap.objs.mapIdx fun k obj =>
    if k == Boot.mainId then { obj with klass := Boot.kernelId }
    else match obj.payload with
    | .cls cp =>
      let cp := if k == Boot.objectId then { cp with superclass := none, includes := [] }
        else if k == Boot.kernelId then
          { cp with superclass := some Boot.basicObjectId, prepends := [Boot.objectId] }
        else if cp.superclass == some Boot.objectId then { cp with superclass := some Boot.kernelId }
        else cp
      { obj with payload := .cls cp }
    | _ => obj } }

private def oldClassReadyB (h : Heap) : Bool :=
  Proof.chainsInB h &&
    (match (h.get Boot.objectId).eigen with
     | some e => (ancestors h e).contains Boot.basicObjectId
     | none => false) &&
    (ancestors h Boot.classId).contains Boot.basicObjectId && eigenSeparateB h && constRefsLiveB h

#guard
  let m := rootDetour
  saturatedB m.heap && (oldClassReadyB m.heap && coreDataB m.heap) && frameOkB m && topScopeB m &&
    methodsExactB ctx0 m && nameFreeB m && missFreeB m && selfLiveB m &&
    localsEmptyB m && queryOkB m && clsQueryOkB m && baseChainsOkB m && nilQueryOkB m &&
    primitiveDispatchB m.heap (nameFreeN ctx0) && primitiveErrorsB m.heap &&
    stringPayloadB m.heap && arrayPayloadB m.heap && hashPayloadB m.heap && mainReadyB m &&
    newDispatchB m.heap (classOf m.heap (.ref Boot.objectId))

#guard ancestors rootDetour.heap Boot.objectId == [Boot.objectId]
#guard !classReadyB rootDetour.heap

theorem class_entry_ordinary {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n k, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx κ name) [] .ivar0 n ∧
      classNamed? n.heap name = some k ∧ OrdinaryClass n.heap k := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  refine ⟨_, m.heap.objs.size, hstep, ?_, ?_, ?_⟩
  · exact FreshClass.state (StateOk_reCtl hm _ []) hr hf ha (ht.heap rfl)
      (FreshClass.nativeFrameB_sound hq) hn hne he
  · exact classNamed_freshClass (hm.runtime hr).classLive hm.core.classReady.chains.boot.2.2.2.2
  · exact FreshClass.ordinary hm.core.classReady hm.sat

#guard match Interp.run 200 (evalFrom rootDetour (.seq [
    .class' "Point" none .nil, .send (some (.const "Point")) "new" [] none])) with
  | .value (.ref o) m => !(ancestors m.heap (m.heap.get o).klass).contains Boot.basicObjectId
  | _ => false

#guard match Interp.run 200 (evalFrom bootMachine (.seq [
    .class' "Point" none .nil, .send (some (.const "Point")) "new" [] none])) with
  | .value (.ref o) m => (ancestors m.heap (m.heap.get o).klass).contains Boot.basicObjectId
  | _ => false

#print axioms class_entry_ordinary
end Ratchet.Denote.Typed
