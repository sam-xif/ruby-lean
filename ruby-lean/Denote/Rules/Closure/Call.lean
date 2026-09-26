import Denote.Rules.Closure.Return

/-! The actual Proc call path: receiver lookup, required-lambda entry, body, and the
block return continuation. The machine intercepts Proc payloads directly in invoke. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem invoke_proc_call {m : Machine} {v : Value} {cl : Closure}
    (hp : procClosure? m.heap v = some cl) (args : List Value) :
    Interp.invoke m v .explicit "call" args none [] =
      Interp.callClosure m cl args (Interp.blockOwner m v) := by
  cases v <;> simp only [procClosure?] at hp
  all_goals try contradiction
  rename_i o
  cases hpay : (m.heap.get o).payload <;> simp only [hpay] at hp
  all_goals try contradiction
  cases hp
  unfold Interp.invoke
  simp only [hpay]
  rfl

theorem step_recv_required_lambda {m : Machine} {v : Value} {cl : Closure} {e : Ratchet.Expr}
    (hp : procClosure? m.heap v = some cl) (hps : cl.params = [])
    (hl : cl.lam = true) (he : cl.body = toRuby e) :
    Interp.stepFn (deliverA (.val v) m [.recvK "call" [] .none .explicit]) =
      .next (pushK [.blkFrameK m.frames.size true (Interp.blockOwner m v) cl []]
        (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [] [])) e)) := by
  change Interp.invoke (deliverA (.val v) m []) v .explicit "call" [] none [] = _
  rw [invoke_proc_call (m := deliverA (.val v) m []) hp []]
  rw [callClosure_required_lambda (deliverA (.val v) m []) cl [] [] _ none none hps hl rfl, he]
  rfl

/-- A complete source send from a stored local, with real receiver evaluation. The
body/return contract is supplied at its actual captured activation, not a value-only type. -/
theorem local_lambda_call_runSpec {m : Machine} {cl : Closure} {e : Ratchet.Expr}
    {Γ : Env} {τ I : Ty} {κ : Ctx} (name : String)
    (hp : procClosure? m.heap (m.getLocal name) = some cl) (hps : cl.params = [])
    (hl : cl.lam = true) (he : cl.body = toRuby e)
    (hb : RunSpec m (pushK [.blkFrameK m.frames.size true (Interp.blockOwner m (m.getLocal name)) cl []]
      (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [] [])) e)) Γ τ κ I) :
    RunSpec m (evalFrom m (.send (some (.var .lvar name)) "call" [] none)) Γ τ κ I := by
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK "call" [] .none .explicit] (evalFrom m (.var .lvar name))) from rfl)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (deliverA (.val (m.getLocal name)) m [.recvK "call" [] .none .explicit]) from by
      simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl,
        List.nil_append] using step_var_ctl (m := pushK [.recvK "call" [] .none .explicit]
        (evalFrom m (.var .lvar name))) (x := name) rfl)
  exact RunSpec.step (by rfl) (step_recv_required_lambda hp hps hl he) hb

#print axioms invoke_proc_call
#print axioms local_lambda_call_runSpec
end Ratchet.Denote.Typed
