import Denote.Rules.Class.ClassActivation
import Denote.Sem.Subclass.SubclassFrame

/-! Run a checked subclass body through the real class frame and restore the caller.
The heap anchor is before subclass allocation; all body changes remain in the output. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet Ratchet.Denote.Typed
open RubyCore.Proof.Judgment (freshModFrame)

theorem body_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {c : Cls} {name : String} {parent eParent : ObjId} {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hkont : m.kont = [])
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get parent).eigen = some eParent)
    (hb : let entry := machine m Boot.objectId m.currentFrame.cref name name parent eParent (toRuby body)
      RunSpec entry (evalFrom entry body) Γb τ κb Ib) :
    RunSpec m (machine m Boot.objectId m.currentFrame.cref name name parent eParent (toRuby body))
      Γ τ (returnScopeCtx κ κb) I := by
  have hpub : Framed m (ClassActivation.publishHeap m (heap m.heap Boot.objectId name name parent eParent)) :=
    framed hm hc hp hn he rfl rfl (.of_eq rfl rfl)
  have hbody := hb.rebase (Framed.of_heap_stack rfl rfl (.of_eq rfl rfl) :
    Framed (pushMethodFrame (ClassActivation.publishHeap m (heap m.heap Boot.objectId name name parent eParent))
      (freshModFrame m.heap.objs.size m.currentFrame.cref))
      (machine m Boot.objectId m.currentFrame.cref name name parent eParent (toRuby body)))
  have hrun := ClassActivation.runSpec hm hpub ht ha hr hw hcl hq hk hΓ hτ hbody
  simpa only [ClassActivation.publishHeap, pushMethodFrame, pushK, evalFrom, machine,
    hkont, List.nil_append] using hrun

#print axioms body_runSpec
end Ratchet.Denote.Subclass
