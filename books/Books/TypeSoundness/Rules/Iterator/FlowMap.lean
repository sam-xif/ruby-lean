import Books.TypeSoundness.Rules.Iterator.MapDispatch
import Books.TypeSoundness.Conformance.Closure.Reify
import Books.TypeSoundness.Rules.Closure.Attached

/-! Source-level attached map/collect blocks: evaluate the receiver, reify the actual block,
dispatch, then use the checked body's live loop invariant. Local facts classify captures
at block entry; the final flow result drops origin claims after arbitrary body effects. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem typed_map_finish {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {name mname : String} {locals names : List String} {body : Checker.Expr} {o : ObjId}
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
  let M := attMachine m [.req name] locals (toRuby body)
  let cl := litClosure m [.req name] locals (toRuby body) false
  have hMs : StateOk κ Γ I M := att_state hm _ _ _
  have hfr : Framed m M := att_framed hm _ _ _
  have hext := att_ext hm [.req name] locals (toRuby body)
  have hr0 := hm.frameInRange
  have hv' : denM (.arrayOf σ) M (.ref o) :=
    denM_pushDead (m := attBase m [.req name] locals (toRuby body)) m.currentFrame
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hr0.2) (denM_ext hext hv)
  have hproc : (M.heap.get m.heap.objs.size).payload = .proc cl := by
    rw [att_payload]; rfl
  have hd' : CaptureSlots names (withoutNames ([name] ++ locals) Γb) M := by
    intro x τ hx
    rw [← hd x τ hx]
    change frameBinds (pushDead _ _) (m.stack.headD 0) x = _
    exact congrArg (fun f : RubyCore.Frame => f.locals.any (·.1 == x))
      (pushDead_getD (m := attBase m [.req name] locals (toRuby body)) (f := m.currentFrame) hr0.2)
  have hinv := typed_map_invoke (m := M) (bo := m.heap.objs.size) (cl := cl) hMs rfl hproc hf hname
    rfl hd' hv' hmain hσ hρ rfl rfl rfl rfl hin hout hfix hb site
  obtain ⟨o', xs, heq, hx, _⟩ := array_payload hv'
  cases heq
  have hclean : ∀ Y, Interp.invoke M (.ref o) site mname [] (some (.ref m.heap.objs.size)) [] =
      .next Y → RootClean Y := by
    intro Y hY
    rw [invoke_array_map hMs hx hproc hf hname site, startIter_map _ _ _ _ rfl] at hY
    by_cases hi : 0 < xs.size
    · rw [mapArrayStep_more (pushMethodFrame M (mapFrame M o mname)) cl M.frames.size o 0 [] xs
        name body hx hi rfl rfl rfl rfl] at hY
      cases hY; exact hMs.rootClean
    · rw [mapArrayStep_end (pushMethodFrame M (mapFrame M o mname)) cl M.frames.size o 0 [] xs
        hx hi] at hY
      cases hY; exact hMs.rootClean
  have hnm : (mname == "lambda" || mname == "proc") = false := by
    rcases hname with rfl | rfl <;> rfl
  rw [finishSend_attached m _ site mname hnm hk hm.rootClean,
    Proof.Root.invoke_frame _ (by intro k hk; simp at hk; subst hk; rfl)]
  cases hrun : Interp.invoke M (.ref o) site mname [] (some (.ref m.heap.objs.size)) [] with
  | next Y =>
    rw [hrun] at hinv
    have hY := hclean Y hrun
    change RunSpec m (Proof.pushRootK _ Y) _ _ _ _
    rw [Proof.pushRootK_quiescent _ Y hY.1 hY.2]
    exact RunSpec.bindAny (S := Y) hinv hMs.rootClean hY
      (by intro k hk; simp at hk; subst hk; rfl)
      (fun a n hn => blockCallK_answer _ hρ hfr hn)
  | unsupported r => trivial
  | done v n => rw [hrun] at hinv; exact hinv.elim
  | uncaught v n => rw [hrun] at hinv; exact hinv.elim
  | stuck r => rw [hrun] at hinv; exact hinv.elim

/-- Sorbet 0.6.13405 assigns map/collect's block the receiver's element type and
uses the checked body result as the output Array element type. Captured types must stay
stable across iterations (clink 228). First-order results survive later body effects. -/
theorem SemFlow.map {κ κr : Ctx} {Γ Γr Γb : Env} {I Ir σ ρ : Ty}
    {facts fr : LocalFacts} {current : Bool} {recv body : Checker.Expr}
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
  apply (hr m hm hfact).bindSpec hm.rootClean (by
    intro k hk
    simp only [List.mem_singleton] at hk
    subst hk
    rfl)
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
end Checker.Soundness.Typed
