import Denote.Rules.Iterator.MapDispatch
import Denote.Sem.Closure.Reify

/-! Source-level attached map/collect blocks: evaluate the receiver, reify the actual block,
dispatch, then use the checked body's live loop invariant. Local facts classify captures
at block entry; the final flow result drops origin claims after arbitrary body effects. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem finishSend_map (m : Machine) (recv : Value) (site : SendSite)
    (name : String) (locals : List String) (body : Ratchet.Expr) (mname : String)
    (hname : mname = "map" ∨ mname = "collect") :
    Interp.finishSend m recv site mname [] (.lit [.req name] locals (toRuby body)) =
      Interp.invoke (reifiedMachine m [.req name] locals (toRuby body) false)
        recv site mname [] (some (.ref m.heap.objs.size)) [] := by
  rcases hname with rfl | rfl <;> cases site <;> rfl

theorem typed_map_finish {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {name mname : String} {locals names : List String} {body : Ratchet.Expr} {o : ObjId}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hf : nameFreeN κ mname = true)
    (hname : mname = "map" ∨ mname = "collect")
    (hd : CaptureSlots names (withoutNames ([name] ++ locals) Γb) m)
    (hv : denM (.arrayOf σ) m (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true) (hρ : FirstOrder ρ = true)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) (site : SendSite) :
    StepSpec m Γ (.arrayOf ρ)
      (Interp.finishSend m (.ref o) site mname [] (.lit [.req name] locals (toRuby body))) κ I := by
  rw [finishSend_map m (.ref o) site name locals body mname hname]
  have hext := reified_ext hm [.req name] locals (toRuby body) false
  have h := typed_map_invoke (bo := m.heap.objs.size)
    (cl := reifiedClosure m [.req name] locals (toRuby body) false)
    (reified_state hm [.req name] locals (toRuby body) false) hk
    (by simp only [reifiedMachine, pushHeap_get_self]) hf hname rfl hd (denM_ext hext hv)
    hmain hσ hρ rfl rfl hin hout hfix hb site
  exact h.rebase (.of_ext hext)

/-- Sorbet 0.6.13405 assigns map/collect's block the receiver's element type and
uses the checked body result as the output Array element type. Captured types must stay
stable across iterations (clink 228). First-order results survive later body effects. -/
theorem SemFlow.map {κ κr : Ctx} {Γ Γr Γb : Env} {I Ir σ ρ : Ty}
    {facts fr : LocalFacts} {current : Bool} {recv body : Ratchet.Expr}
    {name mname : String} {locals names : List String}
    (hr : SemFlow κ Γ I facts recv (.arrayOf σ) current κr Γr Ir fr)
    (hmethod : (mname == "map" || mname == "collect") = true)
    (hf : nameFreeN κr mname = true) (hmain : closureMainB κr Ir = true)
    (hσ : FirstOrder σ = true) (hρ : FirstOrder ρ = true)
    (hn : fr.captureNames? (withoutNames ([name] ++ locals) Γb) = some names)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals locals ++ Γr) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ locals) names Γr Γb = Γr)
    (hb : SemSafeCtxA (closureBodyCtx κr) ([(name, σ)] ++ blockLocals locals ++ Γr) Ir
      body ρ (closureBodyCtx κr) Γb Ir) :
    SemFlow κ Γ I facts (.send (some recv) mname [] (some (.block [.req name] locals body)))
      (.arrayOf ρ) false κr Γr Ir .unknown := by
  intro m hm hfact
  have hname : mname = "map" ∨ mname = "collect" := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using hmethod
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  let pblk : PendingBlk := .lit [.req name] locals (toRuby body)
  apply RunSpec.withPost ?_ (fun _ n _ => ⟨.unknown n, by intro h; cases h⟩)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK mname [] pblk site] (evalFrom m recv)) from rfl)
  apply (hr m hm hfact).bindSpec (by
    intro k hk tag
    simp only [List.mem_singleton] at hk
    subst hk
    simp)
  intro a n hnres
  cases a with
  | val v =>
    obtain ⟨o, xs, rfl, _, _⟩ := array_payload hnres.1.2.1
    let base := deliverA (.val (.ref o)) n []
    have hs : StateOk κr Γr Ir base := StateOk_deliverA (hnres.1.2.2 _ rfl)
    have hd := captureNames_sound ((hnres.2 _ rfl).reCtl (Answer.val (.ref o)).ctl []).1 hn
    have hnext := typed_map_finish hs rfl hf hname hd
      (denM_deliverA.mpr hnres.1.2.1) hmain hσ hρ hin hout hfix hb site
    have hrun : RunSpec base (deliverA (.val (.ref o)) n [.recvK mname [] pblk site])
        Γr (.arrayOf ρ) κr Ir := by
      apply RunSpec.of_stepSpec (by rfl)
      exact hnext
    exact hrun.rebase (hnres.1.1.trans (Framed_reCtl _ _ _))
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hnres.1.1, hnres.1.2.1, fun _ hv => by cases hv⟩

#print axioms typed_map_finish
#print axioms SemFlow.map
end Ratchet.Denote.Typed
