import Denote.Rules.Method.Yield
import Denote.Rules.Method.CallbackState

/-! Source yield with an Integer literal argument. This entry is used by the repeated
yield pilot; general argument evaluation remains a method-body composition obligation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem CallbackFramed.preReCtl {m n : Machine} {c : Ctl} {K : List Kont}
    (h : CallbackFramed (Ratchet.Denote.reCtl m c K) n) : CallbackFramed m n :=
  ⟨(Framed_reCtl _ _ _).trans h.caller, h.stack, h.active, h.bindings⟩

theorem CallbackFramed.proc {m n : Machine} {o : ObjId} {cl : Closure}
    (h : CallbackFramed m n) (hp : (m.heap.get o).payload = .proc cl) :
    (n.heap.get o).payload = .proc cl := by
  have hv := h.caller.procs.payload (.ref o) cl (by simp only [procClosure?, popMethodFrame, hp])
  cases he : (n.heap.get o).payload <;> simp_all [procClosure?, popMethodFrame]

theorem typed_yield_int_continue {m origin : Machine} {κ κout : Ctx} {Γ Γb Γout : Env}
    {I Iout ρ τ : Ty} {cl : Closure} {name : String} {names : List String}
    {body : Ratchet.Expr} {o : ObjId} {K : List Kont}
    (hn : CallbackCaller κ Γ I cl [(name, .int)] names Γb m)
    (hm : FrameInRange m) (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hK : RubyCore.Proof.CatchFree K)
    (hblk : m.currentFrame.blk = some (.ref o)) (hproc : (m.heap.get o).payload = .proc cl)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (hmain : closureMainB κ I = true) (hρ : FirstOrder ρ = true)
    (hin : activationEnvB ([(name, .int)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, .int)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I)
    (hcontinue : ∀ a n, CallbackResultOk m Γ ρ κ I a n →
      RunSpec origin (deliverA a n K) Γout τ κout Iout) (arg : Int) :
    RunSpec origin (pushK K (evalFrom m (.yield' [.int arg]))) Γout τ κout Iout := by
  apply RunSpec.step (by cases K <;> rfl) (show Interp.stepFn _ = .next
    (pushK (.yieldArgK [] [] :: K) (evalFrom m (.int arg))) from rfl)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (deliverA (.val (.int arg)) m (.yieldArgK [] [] :: K)) from rfl)
  apply RunSpec.of_stepSpec (by rfl)
  let base := deliverA (.val (.int arg)) m K
  have hn' : CallbackCaller κ Γ I cl [(name, .int)] names Γb base :=
    ⟨by simpa only [base, popMethodFrame, deliverA] using
      (StateOk_deliverA (a := .val (.int arg)) (K := K) hn.state), hn.capture, hn.slots⟩
  apply typed_yield_continue (m := base) (args := [.int arg]) hn' hm hne rfl hK hblk hproc
    hp he rfl ⟨by simp [denM, isIntV], trivial⟩ hmain hρ hin hout hfix hb
  intro a n hres
  exact hcontinue a n ⟨hres.1.preReCtl, hres.2⟩

#print axioms typed_yield_int_continue
end Ratchet.Denote.Typed
