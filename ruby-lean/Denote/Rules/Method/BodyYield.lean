import Denote.Rules.Method.BodyOrdinary
import Denote.Rules.Method.Yield
import Denote.Rules.Method.RunWith

/-! A checked callback enters the mixed-effect run target through its actual block
continuation. The output retains both complete environments, not just returned values. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem checked_callback_method_runWith {m : Machine} {κ : Ctx} {Γ Γb Γm : Env}
    {I ρ : Ty} {cl : Closure} {ps : List SigParam} {names : List String}
    {args : List Value} {body : Ratchet.Expr} {fr : Ratchet.Frame} {code : ClosureCode}
    {brk : Option FrameId}
    (hn : CallbackCaller κ Γ I cl ps names Γb m)
    (hm : StateOk (callbackMethodCtx κ fr code) Γm I m) (hs : CallbackMethodScope m)
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) (popMethodFrame m) args)
    (hmain : closureMainB κ I = true) (hρ : FirstOrder ρ = true)
    (hin : activationEnvB (ps ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true) (hmethod : activationReturnB Γm = true)
    (hfix : closureReturnEnv (ps.map (·.1) ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) (ps ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) :
    MethodRunWith m
      (pushK [.blkFrameK m.frames.size cl.lam brk cl args]
        (evalFrom (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) body))
      Γ Γm ρ κ (callbackMethodCtx κ fr code) I I (fun _ n => CallbackFramed m n) := by
  apply (hb _ (hn.bodyState hmain hin hargs)).bindMethodWith hm.rootClean (by
    intro k hk
    simp only [List.mem_singleton] at hk
    subst k; rfl)
  intro a n hres
  have hcb := hn.returnResult hm.frameInRange hne hmain hρ hlen hin hout hfix hres
  have hret := hcb.methodResult hn.state hm hmain hs hmethod
  cases a with
  | val v =>
    exact MethodRunWith.step (by rfl) (step_blkFrameK_value n _ cl.lam _ cl args v)
      (MethodRunWith.answer (fun _ _ c k h => h.reCtl c k) ⟨hret, fun _ _ => hcb.1⟩)
  | esc j =>
    obtain ⟨exc, rfl, _⟩ := hres.2.1.only_raise
    exact MethodRunWith.step (by rfl) (show Interp.stepFn _ = .next _ from rfl)
      (MethodRunWith.answer (fun _ _ c k h => h.reCtl c k) ⟨hret, fun _ h => by cases h⟩)

theorem checked_callback_method_run {m : Machine} {κ : Ctx} {Γ Γb Γm : Env}
    {I ρ : Ty} {cl : Closure} {ps : List SigParam} {names : List String}
    {args : List Value} {body : Ratchet.Expr} {fr : Ratchet.Frame} {code : ClosureCode}
    {brk : Option FrameId}
    (hn : CallbackCaller κ Γ I cl ps names Γb m)
    (hm : StateOk (callbackMethodCtx κ fr code) Γm I m) (hs : CallbackMethodScope m)
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) (popMethodFrame m) args)
    (hmain : closureMainB κ I = true) (hρ : FirstOrder ρ = true)
    (hin : activationEnvB (ps ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true) (hmethod : activationReturnB Γm = true)
    (hfix : closureReturnEnv (ps.map (·.1) ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) (ps ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) :
    MethodRunSpec m
      (pushK [.blkFrameK m.frames.size cl.lam brk cl args]
        (evalFrom (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) body))
      Γ Γm ρ κ (callbackMethodCtx κ fr code) I I :=
  (checked_callback_method_runWith hn hm hs hne hlen hargs hmain hρ hin hout hmethod hfix hb).erase

/-- Source yield of a single Integer enters the same target as ordinary assignment.
Arguments follow the measured typed Proc parameter contract (Sorbet 0.6.13405, clink 230).
The checked body, not the code-only closure denotation, supplies callback safety. -/
theorem method_yield_int {m : Machine} {κ : Ctx} {Γ Γb Γm : Env}
    {I ρ : Ty} {cl : Closure} {name : String} {names : List String}
    {body : Ratchet.Expr} {fr : Ratchet.Frame} {code : ClosureCode} {o : ObjId}
    (hn : CallbackCaller κ Γ I cl [(name, .int)] names Γb m)
    (hm : StateOk (callbackMethodCtx κ fr code) Γm I m) (hs : CallbackMethodScope m)
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hblk : m.currentFrame.blk = some (.ref o)) (hproc : (m.heap.get o).payload = .proc cl)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none)
    (hmain : closureMainB κ I = true) (hρ : FirstOrder ρ = true)
    (hin : activationEnvB ([(name, .int)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true) (hmethod : activationReturnB Γm = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, .int)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) (arg : Int) :
    MethodRunSpec m (evalFrom m (.yield' [.int arg]))
      Γ Γm ρ κ (callbackMethodCtx κ fr code) I I := by
  apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.yieldArgK [] []] (evalFrom m (.int arg))) from rfl)
  apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (deliverA (.val (.int arg)) m [.yieldArgK [] []]) from rfl)
  let base := deliverA (.val (.int arg)) m []
  have hn' : CallbackCaller κ Γ I cl [(name, .int)] names Γb base :=
    ⟨by simpa only [base, popMethodFrame, deliverA] using
      (StateOk_deliverA (a := .val (.int arg)) (K := []) hn.state), hn.capture, hn.slots⟩
  have hstep := doYield_required base cl o [name] [.int arg] body [] rfl hblk hproc hp he rfl
    henum hfor
  apply MethodRunSpec.step (by rfl) (show Interp.stepFn
    (deliverA (.val (.int arg)) m [.yieldArgK [] []]) = .next _ from hstep)
  have hs' : CallbackMethodScope base := ⟨hs.self, hs.cref, hs.owner, hs.uncaptured, hs.unaliased⟩
  exact (checked_callback_method_run (args := [.int arg]) hn' (StateOk_deliverA hm) hs' hne rfl
    ⟨by simp [denM, isIntV], trivial⟩ hmain hρ hin hout hmethod hfix hb).rebase
    (.ordinary (Framed_reCtl _ _ _))

#print axioms checked_callback_method_run
#print axioms checked_callback_method_runWith
#print axioms method_yield_int
end Ratchet.Denote.Typed
