import Denote.Rules.Closure.Return
import Denote.Sem.Closure.Dispatch

/-! The actual Proc call path: receiver lookup, required-lambda entry, body, and the
block return continuation. Ordinary lookup must resolve the native Proc call marker. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem invoke_proc_dispatch {m : Machine} {v : Value} {cl : Closure} {name : String}
    (hp : procClosure? m.heap v = some cl) (hr : ProcDispatchReady m.heap name)
    (hn : procCallNameB name = true)
    (hk : classOf m.heap v = Boot.procId) (args : List Value) (site : SendSite := .explicit) :
    Interp.invoke m v site name args none [] =
      Interp.callClosure m cl args (Interp.blockOwner m v) := by
  rcases (show name = "call" ∨ name = "[]" by simpa [procCallNameB] using hn) with hname | hname
  all_goals
    cases v <;> simp only [procClosure?] at hp
    all_goals try contradiction
    rename_i o
    cases hpay : (m.heap.get o).payload <;> simp only [hpay] at hp
    all_goals try contradiction
    cases hp
    obtain ⟨owner, md, hl, hb, hu, hv, hpre, ha⟩ := hr
    have hlook : lookup m.heap (.ref o) name = some (owner, md) := by
      rw [lookup_eq_methodOn, hk]; exact hl
    have hvis : Interp.visError? m (.ref o) site md name = none := by
      simp [Interp.visError?, hv]
    unfold Interp.invoke
    simp only [hpay]
    simp only [Interp.invoke.invokeDispatch, hlook, hu, hpre, Bool.false_eq_true,
      ↓reduceIte, hk, Interp.crubyResolvedShadow, Option.any, ha, hvis, hb,
      Interp.callProcBuiltin, hpay]
    subst hname
    simp [Interp.procCallBid]
    all_goals simp [show Interp.nativeDupBid "Proc#call" = false from by decide +kernel,
      show Interp.nativeCloneBid "Proc#call" = false from by decide +kernel,
      show Interp.requireBid "Proc#call" = false from by decide +kernel,
      show Interp.enumBid "Proc#call" = false from by decide +kernel,
      show Interp.nativeIteratorBid "Proc#call" = false from by decide +kernel,
      show Interp.nativeDupBid "Proc#[]" = false from by decide +kernel,
      show Interp.nativeCloneBid "Proc#[]" = false from by decide +kernel,
      show Interp.requireBid "Proc#[]" = false from by decide +kernel,
      show Interp.enumBid "Proc#[]" = false from by decide +kernel,
      show Interp.nativeIteratorBid "Proc#[]" = false from by decide +kernel]

theorem invoke_proc_call {m : Machine} {v : Value} {cl : Closure}
    (hp : procClosure? m.heap v = some cl) (hr : ProcCallReady m.heap)
    (hk : classOf m.heap v = Boot.procId) (args : List Value) (site : SendSite := .explicit) :
    Interp.invoke m v site "call" args none [] =
      Interp.callClosure m cl args (Interp.blockOwner m v) :=
  invoke_proc_dispatch hp hr rfl hk args site

theorem step_recv_required_lambda {m : Machine} {v : Value} {cl : Closure} {e : Ratchet.Expr}
    (hp : procClosure? m.heap v = some cl) (hr : ProcCallReady m.heap)
    (hk : classOf m.heap v = Boot.procId) (hps : cl.params = [])
    (hl : cl.lam = true) (he : cl.body = toRuby e)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none) :
    Interp.stepFn (deliverA (.val v) m [.recvK "call" [] .none .explicit]) =
      .next (pushK [.blkFrameK m.frames.size true (closureBrk m cl (Interp.blockOwner m v)) cl []]
        (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [] [])) e)) := by
  change Interp.invoke (deliverA (.val v) m []) v .explicit "call" [] none [] = _
  rw [invoke_proc_call (m := deliverA (.val v) m []) hp hr hk []]
  rw [callClosure_required_lambda (deliverA (.val v) m []) cl [] [] _ none none hps hl rfl
    henum hfor, he]
  simp only [requiredClosureFrame, deliverA, definitionFrameId_reCtl]
  rfl

/-- A complete source send from a stored local, with real receiver evaluation. The
body/return contract is supplied at its actual captured activation, not a value-only type. -/
theorem local_lambda_call_runSpec {m : Machine} {cl : Closure} {e : Ratchet.Expr}
    {Γ : Env} {τ I : Ty} {κ : Ctx} (name : String)
    (hp : procClosure? m.heap (m.getLocal name) = some cl) (hr : ProcCallReady m.heap)
    (hk : classOf m.heap (m.getLocal name) = Boot.procId) (hps : cl.params = [])
    (hl : cl.lam = true) (he : cl.body = toRuby e)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none)
    (hb : RunSpec m (pushK [.blkFrameK m.frames.size true
      (closureBrk m cl (Interp.blockOwner m (m.getLocal name))) cl []]
      (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [] [])) e)) Γ τ κ I) :
    RunSpec m (evalFrom m (.send (some (.var .lvar name)) "call" [] none)) Γ τ κ I := by
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK "call" [] .none .explicit] (evalFrom m (.var .lvar name))) from rfl)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (deliverA (.val (m.getLocal name)) m [.recvK "call" [] .none .explicit]) from by
      simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl,
        List.nil_append] using step_var_ctl (m := pushK [.recvK "call" [] .none .explicit]
        (evalFrom m (.var .lvar name))) (x := name) rfl)
  exact RunSpec.step (by rfl) (step_recv_required_lambda hp hr hk hps hl he henum hfor) hb

#print axioms invoke_proc_call
#print axioms invoke_proc_dispatch
#print axioms local_lambda_call_runSpec
end Ratchet.Denote.Typed
