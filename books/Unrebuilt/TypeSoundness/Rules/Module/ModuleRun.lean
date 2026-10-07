import Books.TypeSoundness.Rules.Module.ModuleBodyRun
import Books.TypeSoundness.Rules.Module.ModuleStateEntry

/-! Execute a checked module body in its published header context, restoring the saved
caller activation while retaining the body's outgoing declarations and heap changes. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness
open RubyCore.Proof.Judgment (freshModMachine)

theorem module_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {name : String} {body : Checker.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none)
    (hw : κb.pos.mainWorld = true) (hcl : κ.scope.runtimeClass = none)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (htables : ClassTablesFrame κ name m) (hnative : FreshClass.nativeFrameB κ name = true)
    (hfresh : freshClassNameB κ name = true) (hne : name.isEmpty = false)
    (hplain : unqualifiedClassB name = true) (hframe : moduleHeaderFrameB κ.classes name = true)
    (hb : SemSafeCtxA (moduleHeaderCtx (moduleBodyCtx κ name) name) [] .ivar0 body τ κb Γb Ib) :
    RunSpec m (evalFrom m (.module' name body)) Γ τ (returnScopeCtx κ κb) I := by
  have hn := hm.freshClassName hfresh
  let start := evalFrom m (.module' name body)
  have hstart : StateOk κ Γ I start := StateOk_reCtl hm _ []
  have hentry := FreshModule.state (body := toRuby body) hstart hr hf ha (htables.heap rfl)
    (FreshClass.nativeFrameB_sound hnative) hn hne
  have hheader := FreshModule.publish_header hstart hr hentry hn
    (moduleHeaderFrameB_sound hframe) hplain rfl
  have hrun := FreshModule.body_runSpec hstart ht ha hr hw hcl rfl hq hk hΓ hτ hn (hb _ hheader)
  exact RunSpec.step (answerPoint_evalFrom _ _) (stepFn_module_fresh hm hr hn hne)
    (hrun.rebase (Framed_reCtl m _ []))

#print axioms module_runSpec
end Checker.Soundness.Typed
