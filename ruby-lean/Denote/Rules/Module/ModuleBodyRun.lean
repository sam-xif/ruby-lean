import Denote.Rules.Class.ClassActivation
import Denote.Sem.Module.ModuleFrame

/-! Run a checked module body through the real class frame and restore the caller.
The heap anchor is before module allocation; all body changes remain in the output. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet Ratchet.Denote.Typed
open RubyCore.Proof.Judgment (freshModFrame freshModHeap freshModMachine)

theorem body_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hkont : m.kont = [])
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hb : let entry := freshModMachine m Boot.objectId m.currentFrame.cref name name (toRuby body)
      RunSpec entry (evalFrom entry body) Γb τ κb Ib) :
    RunSpec m (freshModMachine m Boot.objectId m.currentFrame.cref name name (toRuby body))
      Γ τ (returnScopeCtx κ κb) I := by
  have hpub : Framed m (ClassActivation.publishHeap m (freshModHeap m.heap Boot.objectId name name)) :=
    framed hm hn rfl rfl (.of_eq rfl rfl)
  have hbody := hb.rebase (Framed.of_heap_stack rfl rfl (.of_eq rfl rfl) :
    Framed (pushMethodFrame (ClassActivation.publishHeap m (freshModHeap m.heap Boot.objectId name name))
      (freshModFrame m.heap.objs.size m.currentFrame.cref))
      (freshModMachine m Boot.objectId m.currentFrame.cref name name (toRuby body)))
  have hrun := ClassActivation.runSpec hm hpub ht ha hr hw hcl hq hk hΓ hτ hbody
  simpa only [ClassActivation.publishHeap, pushMethodFrame, pushK, evalFrom, freshModMachine,
    hkont, List.nil_append] using hrun

#print axioms body_runSpec
end Ratchet.Denote.FreshModule
