import RubyCore.Interp
/-! Runtime controls for continuation-independent dynamic state.
Run with `lake env lean scripts/probes/dynamic-contexts.lean`.
Only the executable interpreter is imported; the deferred proof repair is independent. -/
namespace DynamicContextControls
open RubyCore
def closure : Closure := { params := [], locals := [], body := .nil, captured := none, home := 0, breakScope := some 7 }
def target : StepResult → Option FrameId
  | .next m => match m.kont with
    | .blkFrameK _ _ brk _ _ :: _ => brk
    | _ => none
  | _ => none
theorem detached_live : target (Interp.callClosure
    { (default : Machine) with liveBreakScopes := [7] } closure [] none) = some 7 := rfl
theorem marker_cannot_revive : target (Interp.callClosure
    { (default : Machine) with kont := [.blockCallK 7] } closure [] none) = none := rfl
theorem expires_normally : Interp.applyKont
    { (default : Machine) with kont := [.blockCallK 7], liveBreakScopes := [7, 8] } .nil =
    .next { (default : Machine) with ctl := .value .nil, liveBreakScopes := [8] } := rfl
theorem expires_on_raise : Interp.unwind
    { (default : Machine) with kont := [.blockCallK 7], liveBreakScopes := [7, 8] } (.raiseJ .nil) =
    .next { (default : Machine) with ctl := .jump (.raiseJ .nil), liveBreakScopes := [8] } := rfl
theorem saved_lifetime (m : Machine) : (Interp.executionOf m).liveBreakScopes = m.liveBreakScopes := rfl
theorem restored_lifetime (m : Machine) (e : Execution) :
    (Interp.restoreExecution m e).liveBreakScopes = e.liveBreakScopes := rfl
theorem detached_inspection (m : Machine) (K : List Kont) :
    ({ m with kont := K } : Machine).objectInspections = m.objectInspections := rfl
theorem inspection_cleanup : Interp.unwind
    { (default : Machine) with kont := [.objectInspectK (.ref 7) .nil [] "" none], objectInspections := [.ref 7, .ref 8] } (.raiseJ .nil) =
    .next { (default : Machine) with ctl := .jump (.raiseJ .nil), objectInspections := [.ref 8] } := rfl
theorem inspection_releases_one :
    ({ (default : Machine) with objectInspections := [.ref 7, .ref 7] } : Machine).leaveObjectInspection (.ref 7) =
    { (default : Machine) with objectInspections := [.ref 7] } := rfl
theorem saved_inspections (m : Machine) : (Interp.executionOf m).objectInspections = m.objectInspections := rfl
theorem restored_inspections (m : Machine) (e : Execution) :
    (Interp.restoreExecution m e).objectInspections = e.objectInspections := rfl
#print axioms detached_live
#print axioms marker_cannot_revive
#print axioms expires_normally
#print axioms expires_on_raise
#print axioms inspection_cleanup
#print axioms inspection_releases_one
end DynamicContextControls
