import Denote.Sem.Class.ClassShape
import Denote.Sem.Class.ClassNew
import Denote.Rules.Method.MethodEntry
import Denote.Rules.Constructor.DefaultNew

/-! The actual new/initialize path: Class#new allocates (callConstruct), then a queued
reflective initialize send dispatches the user initializer. This does not certify an
initializer body: its annotated InitState/run obligation is separate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def ctorAllocated (m : Machine) (k : ObjId) : Machine :=
  { m with heap := pushHeap m.heap { klass := k }, kont := .newK (.ref m.heap.objs.size) :: m.kont }

/-- Two real steps reach the required-parameter frame; native shadows stay unsupported. -/
theorem constructor_entry_stepSpec {κ κ₀ : Ctx} {Γ Γ₀ : Env} {I I₀ τ : Ty} {m : Machine} {k owner : ObjId}
    {md : MethodDef} {names : List String} {args : List Value} {site : SendSite}
    (hm : StateOk κ₀ Γ₀ I₀ m) (hc : PlainAllocator m.heap k)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (hl : Interp.methodOn m.heap k "initialize" = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false)
    (hp : md.params = names.map RubyCore.Param.req) (hcap : md.capturedFrame = none)
    (hdecl : md.declared = []) (ha : args.length = names.length)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hrun : RunSpec m (Interp.withKont (pushMethodFrame (ctorAllocated m k)
        (requiredFrame (.ref m.heap.objs.size) "initialize" md names args))
        (.eval md.body) (.frameK m.frames.size)) Γ τ κ I) :
    StepSpec m Γ τ (Interp.finishSend m (.ref k) site "new" args .none) κ I := by
  obtain ⟨o', md', hl'⟩ := hd.present
  obtain ⟨hb', hu', hv', _, _⟩ := hd.found o' md' hl'
  rw [finishSend_new hc]
  rcases invokeDispatch_classNew (site := site) (args := args)
    (by rw [lookup_eq_methodOn]; exact hl') hb' hu' hv' with ⟨msg, h⟩ | h
  · rw [h]; trivial
  rw [h, callConstruct_plain hc]
  let s := m.heap.objs.size
  let n1 : Machine := { defaultAllocated m k with
    ctl := .send (.ref s) .reflective "initialize" args none [], kont := .newK (.ref s) :: m.kont }
  have hget : n1.heap.get s = { klass := k } := pushHeap_get_self m.heap _
  have he := defaultAllocated_ext hm hc
  have hlk : lookup n1.heap (.ref s) "initialize" = Interp.methodOn m.heap k "initialize" := by
    rw [lookup_eq_methodOn]
    change Interp.methodOn (defaultAllocated m k).heap (classOf n1.heap (.ref s)) "initialize" = _
    simp only [classOf, hget]
    exact he.methodOn_eq hm.core.classReady.chains _ _
  have hs1 : Interp.stepFn n1 =
      Interp.invoke.invokeDispatch n1 (.ref s) .reflective "initialize" args none [] :=
    invoke_payloadNone rfl (by rw [hget])
  rcases invokeDispatch_user (args := args) (site := .reflective) (hlk.trans hl) hb hu
    (by simp [Interp.visError?]) with ⟨msg, h2⟩ | h2
  · exact RunSpec.unsupported rfl (hs1.trans h2)
  · rw [enterUserMethod_required _ _ _ _ _ _ hp hcap hdecl ha hblock hfor] at h2
    exact RunSpec.step rfl (hs1.trans h2) hrun

#print axioms constructor_entry_stepSpec
end Ratchet.Denote.Typed
