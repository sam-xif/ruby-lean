import Denote.Sem.Closure.LocalFacts
import Denote.Rules.Closure.Current
import Denote.Rules.Closure.Call
import Denote.Rules.Closure.ProjectedReturn

/-! A stored call consumes independently tracked origins and physical slots. Unlike a
concrete allocation-prefix pilot, this works at any conformant caller carrying those
facts, including copied bindings. Native lookup comes from StateOk and the call name guard;
body typing is still required at the live captures. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- The zero-argument lambda shape follows the measured Sorbet 0.6.13405 contract
(`lambda { 1 }` has T.proc.returns(Integer), with extra arguments rejected). Origin and
slot facts additionally discharge obligations that a callable value type cannot express.
This is a semantic rule interface; no DJudge constructor is admitted here. -/
theorem tracked_local_lambda_call {κ κb : Ctx} {Γ Γb : Env} {I Ib τ cap selfT : Ty}
    {m : Machine} {facts : LocalFacts} {names : List String} {code : ClosureCode}
    (hm : StateOk κ Γ I m) (hf : LocalFactsOk facts m)
    (hslots : CaptureSlots names Γb m) (name : String) (hx : name ∈ facts.currentProcs)
    (hv : envGet? Γ name = some (.clos code cap selfT)) (hfree : nameFreeN κ "call" = true)
    (hp : code.params = []) (hls : code.locals = []) (hl : code.lam = true)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hr : κ.scope.runtimeMain = true)
    (he : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x)
    (hτ : FirstOrder τ = true)
    (halias : ∀ p ∈ Γ, isAliasTy p.2 = false)
    (hin : ∀ cl, ∀ p ∈ Γ, ∀ v, denM p.2 m v →
      denM p.2 (pushMethodFrame m (requiredClosureFrame m cl [] [])) v)
    (hb : SemSafeCtxA (κ.withoutRuntimeScope.withFrame none) Γ I code.body τ κb Γb Ib)
    (hout : ReframeFO (returnScopeCtx κ κb) I) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hmove : ∀ n x σ, envGet? Γb x = some σ → names.contains x = true → ∀ v,
      denM (stripAlias σ) n v → denM (stripAlias σ) (popMethodFrame n) v) :
    RunSpec m (evalFrom m (.send (some (.var .lvar name)) "call" [] none))
      (captureEnv names Γb) τ (returnScopeCtx κ κb) I := by
  have hval : denM (.clos code cap selfT) m (m.getLocal name) := (hm.env.1 name _ hv).1
  obtain ⟨cl, hproc, hcode, hcap, hklass⟩ := hf.code hx hval
  have hparams : cl.params = [] := by rw [hcode.1, hp]; rfl
  have hlocals : cl.locals = [] := hcode.2.1.trans hls
  have hlam : cl.lam = true := hcode.2.2.2.1.trans hl
  have henv := currentClosureFrame_envOk (ps := []) (args := []) hm
    (hm.runtime hr).captured hcap trivial
    (by simpa [hlocals, blockLocals] using halias)
    (by simpa [hlocals, blockLocals] using hin cl)
  have hstate := requiredClosureFrame_state_of_env (ps := []) hm ht ha
    (ClosureScopeEq.current hm.frameInRange hcap)
    (by rw [hcap]; exact hm.toStateCore.captureLive) henv he
  simp only [hlocals, blockLocals, List.nil_append] at hstate
  apply local_lambda_call_runSpec name hproc (hm.procCall hfree) hklass hparams hlam hcode.2.2.1
    hcode.2.2.2.2.1 hcode.2.2.2.2.2
  apply closure_projected_main_runSpec hm hout ha hr hw hcl hk hcap rfl
    hslots
    (by intros; simp [requiredClosureFrame, hlocals]) true _ cl [] hτ (hb _ hstate)
  intro n _
  exact hmove n

#print axioms tracked_local_lambda_call
end Ratchet.Denote.Typed
