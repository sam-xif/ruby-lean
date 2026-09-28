import Denote.Rules.Closure.Symbol
import Denote.Rules.Method.MethodReturn

/-! The native Symbol closure really evaluates receiver/rest locals and splats the
fresh Array before dispatch. Its all-fuel contract delegates to that actual send,
so the eventual typing rule must establish the forwarded method's domain and arity. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem symbolBody_spec {origin m : Machine} {κ : Ctx} {Γ : Env} {I τ : Ty}
    (name : String) (recv : Value) (rest : ObjId) (args : List Value)
    (hr : m.getLocal "__recv" = recv) (ha : m.getLocal "__rest" = .ref rest)
    (hp : (m.heap.get rest).payload = .arr args.toArray)
    (hcall : StepSpec origin Γ τ
      (Interp.invoke (deliverA (.val (.ref rest)) m []) recv .explicit name args none []) κ I) :
    RunSpec origin (evalFrom m (symbolBody name)) Γ τ κ I := by
  let rk : Kont := .recvK name [.splat (some (.var .lvar "__rest"))] .none .explicit
  let ak : Kont := .argsSplatK recv .explicit name [] [] .none
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ = .next (reCtl m (.eval (.var .lvar "__recv")) [rk]) from rfl)
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ = .next (reCtl m (.value recv) [rk]) from ?_)
  · apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (reCtl m (.eval (.var .lvar "__rest")) [ak]) from rfl)
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (reCtl m (.value (.ref rest)) [ak]) from ?_)
    · apply RunSpec.of_stepSpec (by rfl)
      simpa only [Interp.stepFn, Interp.applyKont, reCtl, ak, Interp.withSpread,
        Interp.spreadA, hp, Interp.spread, Except.map,
        Interp.startArgs, List.nil_append, Interp.finishSend, deliverA, Answer.ctl] using hcall
    · simpa only [getLocal_reCtl, ha, reCtl] using
        (step_var_ctl (m := reCtl m (.eval (.var .lvar "__rest")) [ak]) (x := "__rest") rfl)
  · simpa only [getLocal_reCtl, hr, reCtl] using
      (step_var_ctl (m := reCtl m (.eval (.var .lvar "__recv")) [rk]) (x := "__recv") rfl)

/-- Specialize the forwarding proof to the exact machine callClosure allocates.
No capture equality, one-required-parameter fiction, or empty-rest shortcut is used. -/
theorem symbolEntry_body_spec {origin m : Machine} {κ : Ctx} {Γ : Env} {I τ : Ty}
    (name : String) (recv : Value) (args : List Value)
    (hcall : StepSpec origin Γ τ
      (Interp.invoke (deliverA (.val (.ref m.heap.objs.size)) (symbolEntry m name recv args) [])
        recv .explicit name args none []) κ I) :
    RunSpec origin (evalFrom (symbolEntry m name recv args) (symbolBody name)) Γ τ κ I :=
  symbolBody_spec name recv m.heap.objs.size args
    (by simp [symbolEntry_getLocal]) (by simp [symbolEntry_getLocal])
    (symbolRest_payload m args) hcall

/-- A capture-free body cannot write the caller's locals through its lexical chain.
    Its certified heap effects survive the pop, including the initial rest allocation. -/
theorem symbolEntry_pop_framed {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
    (hm : StateOk κ Γ I m) (name : String) (recv : Value) (args : List Value)
    (h : Framed (symbolEntry m name recv args) n) : Framed m (popMethodFrame n) :=
  (Framed.of_ext (symbolRest_ext hm args)).trans
    (method_pop_framed (m := symbolRest m args) hm.frameInRange.2 rfl h)

theorem symbolEntry_pop_getLocal {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
    (hm : StateOk κ Γ I m) (hu : RootUncaptured m)
    (name : String) (recv : Value) (args : List Value)
    (h : Framed (symbolEntry m name recv args) n) (x : String) :
    (popMethodFrame n).getLocal x = m.getLocal x := by
  rw [method_pop_getLocal (m := symbolRest m args) hm.frameInRange.2 hu rfl h x]
  exact (symbolRest_ext hm args).getLocal_eq x

#print axioms symbolBody_spec
#print axioms symbolEntry_body_spec
#print axioms symbolEntry_pop_framed
#print axioms symbolEntry_pop_getLocal
end Ratchet.Denote.Typed
