import Denote.Rules.Method.Callback
import Denote.Rules.Closure.Return
import Denote.Rules.Primitive.PrimitiveStep

/-! Yield enters the exact checked block and returns through the real block marker.
The method continuation consumes CallbackResultOk, not the false ordinary-method
isolation contract. Arguments have already been evaluated in this entry theorem. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem doYield_required (m : Machine) (cl : Closure) (o : ObjId)
    (names : List String) (args : List Value) (body : Ratchet.Expr) (K : List Kont)
    (hk : m.kont = K) (hblk : m.currentFrame.blk = some (.ref o))
    (hproc : (m.heap.get o).payload = .proc cl)
    (hp : cl.params = names.map RubyCore.Param.req) (he : cl.body = toRuby body)
    (ha : args.length = names.length) :
    Interp.doYield m args = .next
      (pushK (.blkFrameK m.frames.size cl.lam (some (Interp.methodFrameOf m)) cl args :: K)
        (evalFrom (pushMethodFrame m (requiredClosureFrame m cl names args)) body)) := by
  simp only [Interp.doYield, hblk, hproc]
  rw [callClosure_required _ cl names args _ none none hp ha, he]
  simp only [Interp.withKont, pushK, evalFrom, pushMethodFrame, hk, List.nil_append]

/-- Full all-fuel continuation composition. The body is checked against the actual
argument types and live capture; return restores the captured caller and method separately.
Sorbet's typed yield contract inspires the parameter and capture fixed-point premises
(0.6.13405, clink 230); an arrow's partial-return denotation is not used as call safety. -/
theorem typed_yield_continue {m origin : Machine} {κ κout : Ctx} {Γ Γb Γout : Env}
    {I Iout ρ τ : Ty} {cl : Closure} {ps : List SigParam} {names : List String}
    {args : List Value} {body : Ratchet.Expr} {o : ObjId} {K : List Kont}
    (hn : CallbackCaller κ Γ I cl ps names Γb m)
    (hm : FrameInRange m) (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hk : m.kont = K) (hK : RubyCore.Proof.CatchFree K)
    (hblk : m.currentFrame.blk = some (.ref o)) (hproc : (m.heap.get o).payload = .proc cl)
    (hp : cl.params = (ps.map (·.1)).map RubyCore.Param.req) (he : cl.body = toRuby body)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) (popMethodFrame m) args)
    (hmain : closureMainB κ I = true) (hρ : FirstOrder ρ = true)
    (hin : activationEnvB (ps ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv (ps.map (·.1) ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) (ps ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I)
    (hcontinue : ∀ a n, CallbackResultOk m Γ ρ κ I a n →
      RunSpec origin (deliverA a n K) Γout τ κout Iout) :
    StepSpec origin Γout τ (Interp.doYield m args) κout Iout := by
  rw [doYield_required m cl o (ps.map (·.1)) args body K hk hblk hproc hp he (by simpa using hlen)]
  apply (hb _ (hn.bodyState hmain hin hargs)).bindSpec (by
    intro k hmem tag
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp
    · exact hK k hmem tag)
  intro a n hres
  have hret := hn.returnResult hm hne hmain hρ hlen hin hout hfix hres
  cases a with
  | val v =>
    exact RunSpec.step (by rfl) (step_blkFrameK_value n _ cl.lam _ cl args v)
      (hcontinue (.val v) (popMethodFrame n) hret)
  | esc j =>
    exact blkFrameK_escape _ cl.lam _ cl args j hres.2.1
      (hcontinue (.esc j) (popMethodFrame n) hret)

/-- A method that returns this yield's answer can pop its real method marker.
Neither caller conformance nor the block's return type is assumed at this boundary. -/
theorem CallbackResultOk.methodReturn {m n : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {a : Answer} (h : CallbackResultOk m Γ τ κ I a n) (hτ : FirstOrder τ = true)
    (fid : FrameId) :
    RunSpec (popMethodFrame m) (deliverA a n [.frameK fid]) Γ τ κ I := by
  have hresult : ResultOk (popMethodFrame m) Γ τ a (popMethodFrame n) κ I := by
    refine ⟨h.1.caller, ?_, h.2.2⟩
    cases a with
    | val v => exact (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) hτ rfl).mp h.2.1
    | esc j => cases j <;> exact h.2.1
  cases a with
  | val v =>
    exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl)
      (RunSpec.answer hresult)
  | esc j =>
    obtain ⟨exc, rfl, _⟩ := h.2.1.only_raise
    exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl)
      (RunSpec.answer hresult)

#print axioms typed_yield_continue
#print axioms CallbackResultOk.methodReturn
end Ratchet.Denote.Typed
