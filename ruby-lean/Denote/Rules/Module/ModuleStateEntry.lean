import Denote.Rules.Module.ModuleEntry
import Denote.Sem.Module.ModuleState
import Denote.Sem.Module.ModuleHeader
import Denote.Sem.Class.ClassFreshness

/-! Full conformance at the actual module step, publishing only its executed header.
The arbitrary body still needs a checked contract; entry advertises no future methods. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem module_entry_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : freshClassNameB κ name = true) (hne : name.isEmpty = false)
    (hframe : moduleHeaderFrameB κ.classes name = true) (hp : unqualifiedClassB name = true) :
    ∃ n, Interp.stepFn (evalFrom m (.module' name body)) = .next n ∧
      StateOk (moduleHeaderCtx (moduleBodyCtx κ name) name) [] .ivar0 n := by
  have fresh := hm.freshClassName hn
  have hm' : StateOk κ Γ I (evalFrom m (.module' name body)) := StateOk_reCtl hm _ _
  refine ⟨_, stepFn_module_fresh hm hr fresh hne, ?_⟩
  apply FreshModule.publish_header hm' hr
    (FreshModule.state hm' hr hf ha (ht.heap rfl) (FreshClass.nativeFrameB_sound hq) fresh hne)
    fresh (moduleHeaderFrameB_sound hframe) hp rfl

#print axioms module_entry_state
end Ratchet.Denote
