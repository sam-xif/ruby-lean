import Denote.Rules.Closure.FlowArgs

/-! Evaluate an arbitrary current-capture receiver before its arguments. Dispatch receives
the original descriptor and final local facts, even if arguments overwrite its old binding. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemFlow.sendRun {κ κr κa κout : Ctx} {Γ Γr Γa Γout : Env}
    {I Ir Ia Iout τ cap selfT : Ty} {facts fr fa : LocalFacts}
    {recv : Ratchet.Expr} {args : List Ratchet.Expr} {tys : List Ty} {code : ClosureCode} {name : String}
    (hr : SemFlow κ Γ I facts recv (.clos code cap selfT) true κr Γr Ir fr)
    (ha : SemFlowAll κr Γr Ir fr args tys κa Γa Ia fa)
    (ht : ∀ σ ∈ tys, FirstOrder σ = true)
    (finish : ∀ n, StateOk κa Γa Ia n → n.kont = [] → LocalFactsOk fa n → ∀ site v cl,
      procClosure? n.heap v = some cl → ClosureMatches code cl →
      cl.captured = some (n.stack.headD 0) → classOf n.heap v = Boot.procId →
      ∀ vs, DenAll tys n vs → StepSpec n Γout τ
        (Interp.finishSend n v site name vs .none) κout Iout) :
    SemFlow κ Γ I facts (.send (some recv) name args none) τ false κout Γout Iout .unknown := by
  intro m hm hf
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  apply RunSpec.withPost ?_ (fun _ n _ => ⟨.unknown n, by intro h; cases h⟩)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK name (toRubyList args) .none site] (evalFrom m recv)) from rfl)
  apply (hr m hm hf).bindSpec (by
    intro k hk tag
    simp only [List.mem_singleton] at hk
    subst hk
    simp)
  intro a n hn
  cases a with
  | val v =>
    obtain ⟨cl, hp, hcode, hcap, hklass⟩ := ((hn.2 v rfl).2 rfl).code hn.1.2.1
    have hfr : Framed m (deliverA (.val v) n []) := hn.1.1.trans (Framed_reCtl _ _ _)
    have hnext := ha.startArgsKeep
      (P := fun n => procClosure? n.heap v = some cl ∧
        cl.captured = some (n.stack.headD 0) ∧ classOf n.heap v = Boot.procId)
      (recv := v) (name := name) (site := site)
      (StateOk_deliverA (hn.1.2.2 v rfl)) rfl
      ((hn.2 v rfl).reCtl (Answer.val v).ctl []).1 [] [] (by simpa using ht) trivial
      (fun h ⟨hp, hc, hk⟩ => ⟨h.procs.payload v cl hp, by simpa only [h.stack] using hc,
        (h.procs.dispatch v cl hp).trans hk⟩) ⟨hp, hcap, hklass⟩
      (fun n hs hk hf ⟨hp, hc, hklass⟩ vs hv => finish n hs hk hf site v cl hp hcode hc hklass vs hv)
    have hrun : RunSpec (deliverA (.val v) n [])
        (deliverA (.val v) n [.recvK name (toRubyList args) .none site]) Γout τ κout Iout := by
      apply RunSpec.of_stepSpec (by rfl)
      exact hnext
    exact hrun.rebase hfr
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hn.1.1, hn.1.2.1, fun _ hv => by cases hv⟩

#print axioms SemFlow.sendRun
end Ratchet.Denote.Typed
