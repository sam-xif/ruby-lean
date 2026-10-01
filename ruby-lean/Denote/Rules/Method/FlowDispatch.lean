import Denote.Rules.Method.FlowEntry
import Denote.Rules.Method.BodyDispatch

/-! Installed methods with &b use ordinary lookup. Literal allocation supplies both
the exact callback payload and its native class before the real method entry. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemMethodFlow.topInvoke {κ : Ctx} {Γ Γm : Env} {I τ : Ty} {decl : Defn}
    {cb : CheckedCallback κ Γ I} {m : Machine} {cl : Closure} {o : ObjId}
    {localName : String} {callback : Bool} {out : CallbackFacts}
    (hbody : SemMethodFlow cb ⟨"Object", "Object", decl.name, false⟩
      [(localName, .clos cb.code .ivar0 .never)] ⟨[localName]⟩ decl.body τ callback Γm out)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (ht : FirstOrder τ = true)
    (hp : decl.params = [.block (some localName)]) (hd : decl ∈ κ.defs)
    (hc : cl.captured = some (m.stack.headD 0))
    (hslots : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl)
    (hclass : classOf m.heap (.ref o) = Boot.procId) :
    StepSpec m Γ τ (Interp.invoke m m.currentFrame.self .implicit decl.name [] (some (.ref o)) []) κ I := by
  have ready := hm.runtime cb.mainRuntime
  obtain ⟨md, hl, hparams, he, hu, hmcode⟩ := defsOk_lookup hm.defs hd ready.chain
  have h := hbody.callBound hm hk ht (by simpa only [hp, toRubyParams, toRubyParam] using hparams) he
    (hmcode.owner.trans ready.owner.symm) (hmcode.cref.trans ready.cref.symm)
    hmcode.superName hmcode.captured hmcode.declared hc hslots hproc hcode hclass
  rw [ready.self] at h ⊢
  rw [invoke_ordinary_userMethod ready.payload hl hmcode.builtin hu hmcode.fromPrelude rfl
    (by simp [ready.chain, Interp.crubyShadow]; rfl)]
  exact h

theorem SemMethodFlow.topFinishBlock {κ : Ctx} {Γ Γm : Env} {I τ : Ty} {decl : Defn}
    {cb : CheckedCallback κ Γ I} {m : Machine} {localName : String}
    {callback : Bool} {out : CallbackFacts}
    (hbody : SemMethodFlow cb ⟨"Object", "Object", decl.name, false⟩
      [(localName, .clos cb.code .ivar0 .never)] ⟨[localName]⟩ decl.body τ callback Γm out)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (ht : FirstOrder τ = true)
    (hp : decl.params = [.block (some localName)]) (hd : decl ∈ κ.defs) (hlam : cb.code.lam = false)
    (hslots : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cb.code.locals) cb.out) m) :
    StepSpec m Γ τ (Interp.finishSend m m.currentFrame.self .implicit decl.name []
      (.lit (toRubyParams cb.code.params) cb.code.locals (toRuby cb.code.body))) κ I := by
  let ps := toRubyParams cb.code.params
  let ls := cb.code.locals
  let body := toRuby cb.code.body
  let entry := reifiedMachine m ps ls body false
  have hs : StateOk κ Γ I entry := reified_state hm ps ls body false
  have ready := hm.runtime cb.mainRuntime
  have ready' := hs.runtime cb.mainRuntime
  obtain ⟨md, hl, _, _, hu, hcode⟩ := defsOk_lookup hm.defs hd ready.chain
  obtain ⟨md', hl', _, _, _, hcode'⟩ := defsOk_lookup hs.defs hd ready'.chain
  rw [ready.self, finishSend_main_userBlock ps ls body hl hcode.builtin hu hl' hcode'.builtin]
  have h := hbody.topInvoke hs hk ht hp hd (cl := reifiedClosure m ps ls body false)
    (o := m.heap.objs.size) rfl hslots (by simp only [entry, reifiedMachine, pushHeap_get_self])
    ⟨rfl, rfl, rfl, hlam.symm⟩ (by simp [entry, reifiedMachine, classOf, pushHeap_get_self])
  rw [ready'.self] at h
  exact h.rebase (.of_ext (reified_ext hm ps ls body false))

#print axioms SemMethodFlow.topInvoke
#print axioms SemMethodFlow.topFinishBlock
end Ratchet.Denote.Typed
