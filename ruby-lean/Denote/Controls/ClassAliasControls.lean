import Denote.Rules.Class.ClassRun
import Denote.Sem.Class.ClassIdentity
import Denote.Sem.Core.Boot

/-! A dangling global reference can become an alias to a fresh class. It must not silently
invalidate the declared ancestor-name set. This is an injected-heap, not source, control. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def futureAlias : Machine :=
  { bootMachine with
    heap := constSetIn bootMachine.heap Boot.objectId "Future" (.ref bootMachine.heap.objs.size) }

private def oldClassReadyB (h : Heap) : Bool :=
  Proof.chainsInB h &&
    (match (h.get Boot.objectId).eigen with
     | some e => (ancestors h e).contains Boot.basicObjectId
     | none => false) &&
    (ancestors h Boot.classId).contains Boot.basicObjectId && eigenSeparateB h

-- All previous boot checks, including the retained root constructor dispatch.
#guard
  let m := futureAlias
  saturatedB m.heap && (oldClassReadyB m.heap && coreDataB m.heap) && frameOkB m && topScopeB m &&
    methodsExactB ctx0 m && nameFreeB m && missFreeB m && selfLiveB m &&
    localsEmptyB m && queryOkB m && clsQueryOkB m && baseChainsOkB m && nilQueryOkB m &&
    primitiveDispatchB m.heap (nameFreeN ctx0) && primitiveErrorsB m.heap &&
    stringPayloadB m.heap && arrayPayloadB m.heap && hashPayloadB m.heap && mainReadyB m &&
    newDispatchB m.heap (classOf m.heap (.ref Boot.objectId))

#guard constRefsLiveB bootMachine.heap
#guard !constRefsLiveB futureAlias.heap

-- References to already allocated objects may still have multiple constant names.
#guard constRefsLiveB (constSetIn bootMachine.heap Boot.objectId "OldAlias" (.ref Boot.objectId))

theorem class_entry_unique_name {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx κ name) [] .ivar0 n ∧
      ∀ cn, classNamed? n.heap cn = classNamed? n.heap name → cn = name := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  refine ⟨_, hstep, ?_, ?_⟩
  · exact FreshClass.state (StateOk_reCtl hm _ []) hr hf ha (ht.heap rfl)
      (FreshClass.nativeFrameB_sound hq) hn hne he
  · intro cn hcn
    have hname := classNamed_freshClass (name := name) (e := e)
      (hm.runtime hr).classLive hm.core.classReady.chains.boot.2.2.2.2
    exact FreshClass.named_fresh_only hm.core.classReady.constRefs
      hm.core.classReady.chains.boot.2.2.2.2 (hcn.trans hname)

#guard (classNamed? futureAlias.heap "Future").isNone
#guard match Interp.run 200 (evalFrom futureAlias (.seq [
    .class' "Point" none .nil,
    .send (some (.send (some (.const "Point")) "new" [] none)) "is_a?" [.const "Future"] none])) with
  | .value (.bool true) m => classNamed? m.heap "Point" == classNamed? m.heap "Future" &&
      !("Point" :: rootAncestors).contains "Future"
  | _ => false

#print axioms class_entry_unique_name
end Ratchet.Denote.Typed
