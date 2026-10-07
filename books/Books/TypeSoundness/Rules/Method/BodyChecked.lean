import Checker.Check.CheckCallbackBody
import Books.TypeSoundness.Rules.Method.BodyBridge
import Books.TypeSoundness.Rules.Method.BodyEntry

/-! A checked declaration supplies body safety; signatures alone do not. The actual
entry still checks code, parameter shape, owner/cref and callback capture ownership. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem checked_callback_body_context {κ : Ctx} {I : Ty} {decl : Defn}
    (c : CheckedCallbackBody κ I decl) :
    SemMethodBody κ I ⟨"Object", "Object", decl.name, false⟩ c.blockArgs c.blockRet c.params decl.body c.ret c.out :=
  dmethod_context c.judged

theorem checked_callback_call0 {κ : Ctx} {Γ : Env} {I : Ty} {decl : Defn}
    (c : CheckedCallbackBody κ I decl) {cb : CheckedCallback κ Γ I}
    (hparams : c.params = []) (hargs : cb.params.map (·.2) = c.blockArgs) (hret : cb.ret = c.blockRet)
    {m : Machine} {cl : Closure} {o : ObjId} {md : MethodDef}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hp : md.params = toRubyParams decl.params) (he : md.body = toRuby decl.body)
    (howner : md.definee.getD md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none) (hcapture : md.capturedFrame = none) (hdeclared : md.declared = [])
    (hfromBlock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl) :
    StepSpec m Γ c.ret (Interp.enterUserMethod m m.currentFrame.self decl.name md [] (some (.ref o))) κ I := by
  have hb := checked_callback_body_context c cb hargs hret
  rw [hparams] at hb
  have hmd : md.params = [] := by rw [hp, c.paramShape, hparams]; rfl
  exact hb.call0 hm hk c.returnFO hmd he howner hcref hsuper hcapture hdeclared hfromBlock hfor hc hd hproc hcode

#print axioms checked_callback_body_context
#print axioms checked_callback_call0
end Checker.Soundness.Typed
