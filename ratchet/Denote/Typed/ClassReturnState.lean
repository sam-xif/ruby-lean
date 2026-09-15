import Denote.Typed.ClassReturn
import Denote.Typed.MainReturn

/-! Class exit restores the saved activation, not its stale declaration tables. The body
must establish full outgoing conformance; installation metadata alone does not suffice. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

theorem class_pop_main_state {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    {name : String} {e : ObjId} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hu : RootUncaptured m)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hb : Framed (freshClsMachine m Boot.objectId m.currentFrame.cref name name e body) n)
    (hs : StateOk κb Γb Ib n) : StateOk (returnScopeCtx κ κb) Γ I (popMethodFrame n) := by
  obtain ⟨_, scope⟩ := hs.classRuntime name hq
  exact restore_main_state hm ht ha hr hw hcl hk (class_pop_framed hm hn he hb)
    (class_pop_currentFrame hm.frameInRange hb) (class_pop_envOk hm hu hn he hb hΓ) scope.phase hs

theorem class_body_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {name : String} {e : ObjId} {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hkont : m.kont = [])
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hb : let entry := freshClsMachine m Boot.objectId m.currentFrame.cref name name e (toRuby body)
      RunSpec entry (evalFrom entry body) Γb τ κb Ib) :
    RunSpec m (freshClsMachine m Boot.objectId m.currentFrame.cref name name e (toRuby body))
      Γ τ (returnScopeCtx κ κb) I := by
  let published := { m with heap := freshClsHeap m.heap Boot.objectId name name e }
  let frame := freshModFrame m.heap.objs.size m.currentFrame.cref
  let entry := freshClsMachine m Boot.objectId m.currentFrame.cref name name e (toRuby body)
  have hentry : Framed (pushMethodFrame published frame) entry :=
    .of_heap_stack rfl rfl (.of_eq rfl rfl)
  have hback : Framed entry (pushMethodFrame published frame) :=
    .of_heap_stack rfl rfl (.of_eq rfl rfl)
  have hbody : RunSpec (pushMethodFrame published frame)
      (evalFrom (pushMethodFrame published frame) body) Γb τ κb Ib := hb.rebase hentry
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (hm.runtime hr).captured
  have hrun := methodFrame_runSpec (m := published) hm.frameInRange.2 (f := frame) rfl hτ hbody
    (fun n v result => class_pop_main_state hm ht ha hr hw hcl hu hq hk hΓ hn he
      (hback.trans result.1) (result.2.2 v rfl))
  have hout := hrun.rebase (Framed.of_freshClass hm hn he rfl rfl (.of_eq rfl rfl))
  simpa only [published, frame, pushMethodFrame, pushK, evalFrom, freshClsMachine,
    Interp.withKont, hkont, List.nil_append] using hout

#print axioms class_pop_main_state
#print axioms class_body_runSpec
end Ratchet.Denote.Typed
