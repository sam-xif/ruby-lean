import Books.TypeSoundness.Conformance.Module.ModuleHeaderActual
import Books.TypeSoundness.Rules.Module.ModuleCallbacks
import Books.TypeSoundness.Rules.Class.ClassActivation
import Books.TypeSoundness.Conformance.Class.ClassFreshness

/-! Fresh module execution over the actual registration heap: entry, the native
const_added callback, the published header body and the original frame return. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem module_actual_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
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
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true)
    (hb : SemSafeCtxA (moduleHeaderCtx (moduleBodyCtx κ name) name) [] .ivar0 body τ κb Γb Ib) :
    RunSpec m (evalFrom m (.module' name body)) Γ τ (returnScopeCtx κ κb) I := by
  have hn := hm.freshClassName hfresh
  have hmain := hm.runtime hr
  let start := evalFrom m (.module' name body)
  have hstart : StateOk κ Γ I start := StateOk_reCtl hm _ []
  have hs := FreshModuleActual.stepFn_fresh (m := start) (body := toRuby body)
    ((StateOk_reCtl hm (.eval (toRuby (.module' name body))) []).runtime hr) hn
  have hh : FreshModuleActual.heap start name = FreshModuleActual.heap m name := rfl
  rw [hh] at hs
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hol := lt_size_of_classPayload hmain.classLive
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hol
  have hc := hm.core.classReady.chains
  have hheader := FreshModuleActual.header (body := toRuby body) hstart hr hf ha
    (htables.heap rfl) (FreshClass.nativeFrameB_sound hnative) hn hne hreach hplain
    (moduleHeaderFrameB_sound hframe)
  have hbody := hb _ (StateOk_reCtl hheader (.eval (toRuby body)) [])
  let pub := ClassActivation.publishHeap start (FreshModuleActual.heap m name)
  have hp : Framed start pub :=
    FreshModuleActual.framed hstart htop hn rfl rfl (.of_eq rfl rfl)
  have hrun := ClassActivation.runSpec (k := m.heap.objs.size) hstart hp ht ha hr hw hcl hq hk hΓ hτ
    (hbody.rebase (Framed.of_heap_stack rfl rfl (.of_eq rfl rfl)))
  have hcb := module_callbacks_runSpec (m := { start with heap := FreshModuleActual.heap m name })
    (k := m.heap.objs.size) (name := name) (body := toRuby body)
    ((FreshModuleActual.classHooksQuietB_eq hc hm.sat hd).trans hmain.classHooks)
    (FreshModuleActual.chainsIn hc hd)
    ((FreshModuleActual.classPayload_live hd hol).trans hmain.classLive) hmain.phase hmain.origin
    hrun
  exact RunSpec.step (answerPoint_evalFrom _ _) hs (hcb.rebase (Framed_reCtl m _ []))

#print axioms module_actual_runSpec
end Checker.Soundness.Typed
