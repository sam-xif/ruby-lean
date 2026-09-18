import Denote.Sem.Class.ClassFreshness
import Denote.Controls.ClassStateControls
import Ratchet.Static.CtxEq

/-! Old full-boot conformance permitted extra constants, even non-class values. The new
bound rejects them; unlike a declaration-table check it justifies fresh entry for any name. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def occupied : Machine :=
  { bootMachine with heap := constSetIn bootMachine.heap Boot.objectId "Occupied" (.int 1) }

-- Every check before adding the global-name bound still passes.
#guard
  let m := occupied
  saturatedB m.heap && coreOkB m.heap && frameOkB m && topScopeB m &&
    methodsExactB ctx0 m && nameFreeB m && missFreeB m && selfLiveB m &&
    localsEmptyB m && queryOkB m && clsQueryOkB m && baseChainsOkB m && nilQueryOkB m &&
    primitiveDispatchB m.heap (nameFreeN ctx0) && primitiveErrorsB m.heap &&
    stringPayloadB m.heap && arrayPayloadB m.heap && hashPayloadB m.heap && mainReadyB m &&
    newDispatchB m.heap (classOf m.heap (.ref Boot.objectId))

#guard match Interp.run 20 (evalFrom occupied (.class' "Occupied" none .nil)) with
  | .uncaught ex n => classOf n.heap ex == Boot.typeErrorId
  | _ => false

#guard globalConstsOkB ctx0.pos.globalConsts bootMachine.heap
#guard !globalConstsOkB (ctx0.pos.globalConsts.filter (· != "Object")) bootMachine.heap
#guard !globalConstsOkB ctx0.pos.globalConsts occupied.heap
#guard globalConstsOkB ("Occupied" :: ctx0.pos.globalConsts) occupied.heap
#guard freshClassNameB ctx0 "Occupied"
#guard !freshClassNameB ctx0 "Object" && !freshClassNameB ctx0 "T"
#guard !freshClassNameB (classBodyCtx ctx0 "Occupied") "Occupied"
#guard freshClassNameB (classBodyCtx ctx0 "Occupied") "AnotherClass"
#guard !ctxEqB ctx0 { ctx0 with pos := { ctx0.pos with globalConsts := [] } }
#guard !ctxEqB { ctx0 with pos := { ctx0.pos with globalConsts := [] } } ctx0

-- No particular name, body, or preallocated class id appears in this entry theorem.
theorem fresh_guard_entry {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : freshClassNameB κ name = true) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx κ name) [] .ivar0 n :=
  class_entry_state hm hr hf ha ht hq (hm.freshClassName hn) hne

#print axioms fresh_guard_entry
end Ratchet.Denote.Typed
