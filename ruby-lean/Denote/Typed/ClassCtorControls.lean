import Denote.Typed.ClassRun
import Denote.Sem.ClassNewEntry
import Denote.Sanity

/-! Constructor dispatch is a separate obligation from class entry and instance code.
Retagging Class#new leaves the old boot contract intact but changes the actual result. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def wrongNew : Machine :=
  { bootMachine with
    heap := defineMethod bootMachine.heap Boot.classId "new"
      { owner := Boot.classId, params := [], body := .nil, builtin := some "Object#nil?" } }

-- Full previous boot conjunction, not only method-table or framing checks.
#guard
  let m := wrongNew
  saturatedB m.heap && coreOkB m.heap && frameOkB m && topScopeB m &&
    methodsExactB ctx0 m && nameFreeB m && missFreeB m && selfLiveB m &&
    localsEmptyB m && queryOkB m && clsQueryOkB m && baseChainsOkB m && nilQueryOkB m &&
    primitiveDispatchB m.heap (nameFreeN ctx0) && primitiveErrorsB m.heap &&
    stringPayloadB m.heap && arrayPayloadB m.heap && hashPayloadB m.heap && mainReadyB m

#guard clsQueryOkB bootMachine
#guard !newDispatchB wrongNew.heap (classOf wrongNew.heap (.ref Boot.objectId))

-- Existing prelude constructors are deliberately outside the root-only requirement.
#guard ["Range", "Struct"].all fun cn =>
  (classNamed? bootMachine.heap cn).any fun k =>
    !newDispatchB bootMachine.heap (classOf bootMachine.heap (.ref k))

theorem class_entry_new_dispatch {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hw : κ.pos.mainWorld = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hnew : nameFreeN κ "new" = true) (hquiet : FreshClass.NativeQuiet name "new") :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx κ name) [] .ivar0 n ∧
      NewDispatch n.heap (classOf n.heap n.currentFrame.self) := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  refine ⟨_, hstep, ?_, ?_⟩
  · exact FreshClass.state (StateOk_reCtl hm _ []) hr hf ha (ht.heap rfl)
      (FreshClass.nativeFrameB_sound hq) hn hne he
  · have hframe := FreshClass.current_frame (m := evalFrom m (.class' name none body))
      (name := name) (e := e) (body := toRuby body)
    simp only [evalFrom, currentFrame_reCtl] at hframe ⊢
    rw [hframe]
    exact FreshClass.new_dispatch hm.core.classReady.chains hm.sat he hne hquiet
      ((hm.mainSite hw).newDispatch hnew)

#guard match Interp.run 150 (evalFrom wrongNew (.seq [
    .class' "Point" none .nil, .send (some (.const "Point")) "new" [] none])) with
  | .value (.bool false) _ => true
  | _ => false

#guard match Interp.run 150 (evalFrom bootMachine (.seq [
    .class' "Point" none .nil, .send (some (.const "Point")) "new" [] none])) with
  | .value v m => isAName m.heap v "Point"
  | _ => false

#print axioms class_entry_new_dispatch
end Ratchet.Denote.Typed
