import Books.TypeSoundness.Rules.Method.CallbackFacts

/-! Method-local flow carries callback aliases separately from value types. Sorbet
0.6.13405 accepts copies and repeated calls, including after overwriting the original
binding; nil overwrites invalidate that local (clinks 240–241). -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def SemMethodFlow {κ : Ctx} {Γ : Env} {I : Ty} (cb : CheckedCallback κ Γ I) (fr : Checker.Frame)
    (Γm : Env) (facts : CallbackFacts) (e : Checker.Expr) (τ : Ty) (callback : Bool)
    (Γm' : Env) (out : CallbackFacts) : Prop :=
  ∀ origin m, MethodActivation cb fr Γm origin m → CallbackFactsOk facts m →
    MethodRunWith m (evalFrom m e) Γ Γm' τ κ (callbackMethodCtx κ fr cb.code) I I
      (CallbackPost out callback)

theorem SemMethodFlow.erase {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e : Checker.Expr}
    {out : CallbackFacts} {callback : Bool}
    (h : SemMethodFlow cb fr Γm .empty e τ callback Γm' out) : SemMethod cb fr Γm e τ Γm' :=
  fun origin m hm => (h origin m hm (.empty m)).erase

/-- An arbitrary certified method expression may overwrite any local. Recovering
aliases needs its own proof; it cannot be inferred from its outgoing closure types. -/
theorem SemMethodFlow.embed {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e : Checker.Expr}
    (facts : CallbackFacts) (h : SemMethod cb fr Γm e τ Γm') :
    SemMethodFlow cb fr Γm facts e τ false Γm' .empty :=
  fun origin m hm _ => (h origin m hm).withPost
    (fun _ n _ => ⟨.empty n, by intro h; cases h⟩)

theorem SemMethodFlow.leaf {κ : Ctx} {Γ Γm : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e : Checker.Expr}
    {facts : CallbackFacts} {callback : Bool}
    (h : ∀ origin m, MethodActivation cb fr Γm origin m → CallbackFactsOk facts m → ∃ v,
      Interp.stepFn (evalFrom m e) = .next (deliverA (.val v) m []) ∧
      denM τ m v ∧ (callback = true → MethodCallbackReceiver m v)) :
    SemMethodFlow cb fr Γm facts e τ callback Γm facts := by
  intro origin m hm hf
  obtain ⟨v, hs, hd, hv⟩ := h origin m hm hf
  apply MethodRunWith.step (answerPoint_evalFrom _ _) hs
  exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k)
    ⟨⟨.refl m, hd, fun _ _ => ⟨hm.caller, hm.method⟩⟩, fun _ he => by cases he; exact ⟨hf, hv⟩⟩

theorem SemMethodFlow.intLit {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} (facts : CallbackFacts) (n : Int) :
    SemMethodFlow cb fr Γm facts (.int n) .int false Γm facts := by
  apply SemMethodFlow.leaf
  intro _ m _ _
  exact ⟨.int n, rfl, by simp [denM, isIntV], by intro h; cases h⟩

theorem SemMethodFlow.nilLit {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} (facts : CallbackFacts) :
    SemMethodFlow cb fr Γm facts .nil .nilT false Γm facts := by
  apply SemMethodFlow.leaf
  intro _ m _ _
  exact ⟨.nil, rfl, by simp [denM, isNilV], by intro h; cases h⟩

theorem SemMethodFlow.var {κ : Ctx} {Γ Γm : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {x : String} (facts : CallbackFacts)
    (hg : envGet? Γm x = some τ) (ha : isAliasTy τ = false) :
    SemMethodFlow cb fr Γm facts (.var .lvar x) τ (facts.aliases.contains x) Γm facts := by
  apply SemMethodFlow.leaf
  intro _ m hm hf
  exact ⟨m.getLocal x, stepFn_var m x, denM_getLocal hm.method hg ha,
    fun hx => hf x (by simpa using hx)⟩

theorem SemMethodFlow.vasgn {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e : Checker.Expr} {x : String}
    {facts out : CallbackFacts} {callback : Bool}
    (h : SemMethodFlow cb fr Γm facts e τ callback Γm' out)
    (hc : capStale x τ τ = false) (ha : isAliasTy τ = false)
    (hk : capStaleCtx x τ (callbackMethodCtx κ fr cb.code) = false)
    (hi : killClosOverSpine I x τ = I) :
    SemMethodFlow cb fr Γm facts (.vasgn .lvar x e) τ callback (envAfter Γm' x τ)
      (out.write x callback) := by
  intro origin m hm hf
  apply MethodRunWith.step (answerPoint_evalFrom _ _) (show Interp.stepFn _ = .next
    (pushK [.asgnK .lvar x] (evalFrom m e)) from rfl)
  apply (h origin m hm hf).bind hm.method.rootClean (catchFree_asgnK x)
  intro a n hr
  cases a with
  | val v =>
    have hn := hm.after hr.1
    have hd : denM τ n v := hr.1.2.1
    have hs : StateOk (callbackMethodCtx κ fr cb.code) (envAfter Γm' x τ) I (n.setLocal x v) := by
      simpa only [envAfter, hi] using StateOk_setLocal hn.method hd hc hk
        (ρ := τ) (by cases τ <;> simp_all [stripAlias, isAliasTy])
        (by intro y σ hy; rw [hy] at ha; simp [isAliasTy] at ha)
    have hw := Framed_setLocal n x v hn.method.headAlias
    have hcaller := ordinary_caller_state hn.originState hn.caller hn.uncaptured cb.main
      cb.callerTypes hn.fresh hn.framed hw hs
    have hp := hr.2 v rfl
    apply MethodRunWith.step (next := deliverA (.val v) (n.setLocal x v) []) (by rfl) (by
      change StepResult.next (deliverA (.val v) ((reCtl n (.value v) []).setLocal x v) []) = _
      rw [setLocal_reCtl]; rfl)
    exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k)
      ⟨⟨hr.1.1.trans (.ordinary hw), denM_setLocal hd hc hd,
        fun _ hv => by cases hv; exact ⟨hcaller, hs⟩⟩,
       fun _ hv => by cases hv; exact ⟨hp.1.write hn.method.frameInRange.2 hn.method.headAlias x v callback hp.2,
         fun h => (hp.2 h).setLocal x v⟩⟩
  | esc j =>
    apply MethodRunWith.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
    exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k)
      ⟨⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩, fun _ hv => by cases hv⟩

#print axioms SemMethodFlow.vasgn
#print axioms SemMethodFlow.var
end Checker.Soundness.Typed
