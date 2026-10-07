import Books.TypeSoundness.Rules.Method.BodyYieldOne

/-! Assignment around a callback-capable expression. Sorbet 0.6.13405 accepts a local
changing from nil to an Integer yield result; captured caller types remain fixed. The
ordinary assignment guards still protect closures, aliases, context and ivar types. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem SemMethod.vasgn {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e : Checker.Expr} {x : String}
    (h : SemMethod cb fr Γm e τ Γm')
    (hc : capStale x τ τ = false) (ha : isAliasTy τ = false)
    (hk : capStaleCtx x τ (callbackMethodCtx κ fr cb.code) = false)
    (hi : killClosOverSpine I x τ = I) :
    SemMethod cb fr Γm (.vasgn .lvar x e) τ (envAfter Γm' x τ) := by
  intro origin m hm
  apply MethodRunSpec.step (answerPoint_evalFrom _ _) (show Interp.stepFn _ = .next
    (pushK [.asgnK .lvar x] (evalFrom m e)) from rfl)
  apply (h origin m hm).bind hm.method.rootClean (catchFree_asgnK x)
  intro a n hr
  cases a with
  | val v =>
    have hn := hm.after hr
    have hd : denM τ n v := hr.2.1
    have hs : StateOk (callbackMethodCtx κ fr cb.code) (envAfter Γm' x τ) I (n.setLocal x v) := by
      simpa only [envAfter, hi] using StateOk_setLocal hn.method hd hc hk
        (ρ := τ) (by cases τ <;> simp_all [stripAlias, isAliasTy])
        (by intro y σ hy; rw [hy] at ha; simp [isAliasTy] at ha)
    have hf := Framed_setLocal n x v hn.method.headAlias
    have hcaller := ordinary_caller_state hn.originState hn.caller hn.uncaptured cb.main
      cb.callerTypes hn.fresh hn.framed hf hs
    apply MethodRunSpec.step (next := deliverA (.val v) (n.setLocal x v) []) (by rfl) (by
      change StepResult.next (deliverA (.val v) ((reCtl n (.value v) []).setLocal x v) []) = _
      rw [setLocal_reCtl]; rfl)
    exact MethodRunSpec.answer ⟨hr.1.trans (.ordinary hf), denM_setLocal hd hc hd,
      fun _ hv => by cases hv; exact ⟨hcaller, hs⟩⟩
  | esc j =>
    apply MethodRunSpec.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
    apply MethodRunSpec.answer (a := .esc j) (n := n)
    exact ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

#print axioms SemMethod.vasgn
end Checker.Soundness.Typed
