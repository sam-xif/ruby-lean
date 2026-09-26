import Ratchet.Check.CheckMethodFlow
import Denote.Rules.Method.FlowBridge
import Denote.Rules.Method.FlowEntry

/-! A code-polymorphic checked definition supplies the body at the actual callback
code. The installed source and real entry metadata remain separate obligations. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem checked_bound_callback_body_uniform {κ : Ctx} {I : Ty} {decl : Defn}
    (c : CheckedBoundCallbackBody κ I decl) :
    ∀ code, SemMethodFlowBody κ I ⟨"Object", "Object", decl.name, false⟩ c.blockArgs c.blockRet
      [(c.localName, .clos code .ivar0 .never)] ⟨[c.localName]⟩ decl.body c.ret c.callback
      (c.out.instantiate code) c.outFacts :=
  fun code => dmethodFlow_context (c.judged code)

theorem checked_bound_callback_body_context {κ : Ctx} {I : Ty} {decl : Defn}
    (c : CheckedBoundCallbackBody κ I decl) {Γ : Env} (cb : CheckedCallback κ Γ I)
    (hp : cb.params.map (·.2) = c.blockArgs) (hr : cb.ret = c.blockRet) :
    SemMethodFlow cb ⟨"Object", "Object", decl.name, false⟩
      [(c.localName, .clos cb.code .ivar0 .never)] ⟨[c.localName]⟩ decl.body c.ret c.callback
      (c.out.instantiate cb.code) c.outFacts :=
  checked_bound_callback_body_uniform c cb.code cb hp hr

theorem checked_bound_callback_call {κ : Ctx} {Γ : Env} {I : Ty} {decl : Defn}
    (c : CheckedBoundCallbackBody κ I decl) {cb : CheckedCallback κ Γ I}
    (hargs : cb.params.map (·.2) = c.blockArgs) (hret : cb.ret = c.blockRet)
    {m : Machine} {cl : Closure} {o : ObjId} {md : MethodDef}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hp : md.params = toRubyParams decl.params) (he : md.body = toRuby decl.body)
    (howner : md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none) (hcapture : md.capturedFrame = none) (hdeclared : md.declared = [])
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl)
    (hclass : classOf m.heap (.ref o) = Boot.procId) :
    StepSpec m Γ c.ret (Interp.enterUserMethod m m.currentFrame.self decl.name md [] (some (.ref o))) κ I := by
  have hb := checked_bound_callback_body_context c cb hargs hret
  have hmd : md.params = [.block (some c.localName)] := by rw [hp, c.paramShape]; rfl
  exact hb.callBound hm hk c.returnFO hmd he howner hcref hsuper hcapture hdeclared hc hd hproc hcode hclass

#print axioms checked_bound_callback_body_uniform
#print axioms checked_bound_callback_body_context
#print axioms checked_bound_callback_call
end Ratchet.Denote.Typed
