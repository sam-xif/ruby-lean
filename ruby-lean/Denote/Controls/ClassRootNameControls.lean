import Denote.Rules.Class.ClassRun
import Denote.Sem.Core.Boot

/-! Root names can be redirected while existing primitive ancestor-name rows remain
correct. Fresh ordinary classes inherit Object's physical chain, not those redirects. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def redirectedKernel : Machine :=
  let h := bootMachine.heap
  let proxy := h.objs.size
  let objs := h.objs.mapIdx fun k obj =>
    if builtinBases.any (fun row => row.1 == k) then
      match obj.payload with
      | .cls cp => { obj with payload := .cls { cp with includes := proxy :: cp.includes } }
      | _ => obj
    else obj
  let proxyObj : Object :=
    { klass := Boot.moduleId, payload := .cls { superclass := none, name := "KernelProxy", isModule := true } }
  let h : Heap := ⟨objs.push proxyObj⟩
  { bootMachine with heap := constSetIn h Boot.objectId "Kernel" (.ref proxy) }

#guard
  let m := redirectedKernel
  saturatedB m.heap && (classReadyB m.heap && coreDataB m.heap) && frameOkB m && topScopeB m &&
    methodsExactB ctx0 m && nameFreeB m && missFreeB m && selfLiveB m &&
    localsEmptyB m && queryOkB m && clsQueryOkB m && baseChainsOkB m && nilQueryOkB m &&
    primitiveDispatchB m.heap (nameFreeN ctx0) && primitiveErrorsB m.heap &&
    stringPayloadB m.heap && arrayPayloadB m.heap && hashPayloadB m.heap && mainReadyB m &&
    newDispatchB m.heap (classOf m.heap (.ref Boot.objectId))

#guard rootNamesB bootMachine.heap
#guard !rootNamesB redirectedKernel.heap
#guard !rootNamesB (constSetIn bootMachine.heap Boot.objectId "OtherRoot" (.ref Boot.objectId))
#guard rootNamesB (constSetIn bootMachine.heap Boot.objectId "Text" (.ref Boot.stringId))

theorem class_entry_named_ancestry {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n k, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx κ name) [] .ivar0 n ∧ classNamed? n.heap name = some k ∧
      (∀ cn ∈ name :: rootAncestors, ∃ j, classNamed? n.heap cn = some j ∧
        (ancestors n.heap k).contains j = true) ∧
      (∀ cn j, classNamed? n.heap cn = some j → (ancestors n.heap k).contains j = true →
        cn ∈ name :: rootAncestors) := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  refine ⟨_, m.heap.objs.size, hstep, ?_, ?_, ?_⟩
  · exact FreshClass.state (StateOk_reCtl hm _ []) hr hf ha (ht.heap rfl)
      (FreshClass.nativeFrameB_sound hq) hn hne he
  · exact classNamed_freshClass (hm.runtime hr).classLive hm.core.classReady.chains.boot.2.2.2.2
  · exact FreshClass.named_chain hm.core.classReady hm.sat hm.core.rootNames (hm.runtime hr).classLive hn

#guard match Interp.run 200 (evalFrom redirectedKernel (.seq [
    .class' "Point" none .nil,
    .send (some (.send (some (.const "Point")) "new" [] none)) "is_a?" [.const "Kernel"] none])) with
  | .value (.bool false) _ => true
  | _ => false

#guard match Interp.run 200 (evalFrom bootMachine (.seq [
    .class' "Point" none .nil,
    .send (some (.send (some (.const "Point")) "new" [] none)) "is_a?" [.const "Kernel"] none])) with
  | .value (.bool true) _ => true
  | _ => false

#print axioms class_entry_named_ancestry
end Ratchet.Denote.Typed
