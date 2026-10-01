import Denote.Sem.Class.ClassHeaderStateActual
import Denote.Sem.Class.ClassFreshness
import Denote.Rules.Class.ClassActivation
import Denote.Rules.Class.ClassEntry

/-! Fresh class execution over the actual registration heap: entry, both native
callbacks, the published header body and the original frame return. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshModFrame)

theorem class_actual_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (hin : κ.pos.mainWorld = true)
    (hw : κb.pos.mainWorld = true) (hcl : κ.scope.runtimeClass = none)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (htables : ClassTablesFrame κ name m) (hnative : FreshClass.nativeFrameB κ name = true)
    (hfresh : freshClassNameB κ name = true) (hne : name.isEmpty = false)
    (hnew : nameFreeN κ "new" = true) (hquiet : classNativeQuietB name "new" = true)
    (hplain : unqualifiedClassB name = true) (hframe : headerTableFrameB κ.classes name = true)
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true)
    (hb : SemSafeCtxA (classHeaderCtx (classBodyCtx κ name) name) [] .ivar0 body τ κb Γb Ib) :
    RunSpec m (evalFrom m (.class' name none body)) Γ τ (returnScopeCtx κ κb) I := by
  have hn := hm.freshClassName hfresh
  obtain ⟨e, he, hs⟩ := stepFn_class_fresh (body := body) hm hr hn hne
  let start := evalFrom m (.class' name none body)
  have hstart : StateOk κ Γ I start := StateOk_reCtl hm _ []
  have hmain := hm.runtime hr
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hol := lt_size_of_classPayload hmain.classLive
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hol
  have hc := hm.core.classReady.chains
  have hel := hc.eigen _ hol _ he
  have hheader := FreshClassActual.header (body := toRuby body) hstart hr hf ha hin
    (htables.heap rfl) (FreshClass.nativeFrameB_sound hnative) hn hne he hreach hnew hquiet hplain
    (headerTableFrameB_sound hframe)
  have hbody := hb _ (StateOk_reCtl hheader (.eval (toRuby body)) [])
  let pub := ClassActivation.publishHeap start (FreshClassActual.heap m name e)
  have hp : Framed start pub :=
    FreshClassActual.framed hstart htop hn he rfl rfl (.of_eq rfl rfl)
  have hrun := ClassActivation.runSpec (k := m.heap.objs.size) hstart hp ht ha hr hw hcl hq hk hΓ hτ
    (hbody.rebase (Framed.of_heap_stack rfl rfl (.of_eq rfl rfl)))
  have hcb := class_callbacks_runSpec (m := { start with heap := FreshClassActual.heap m name e })
    (k := m.heap.objs.size) (name := name) (body := toRuby body)
    ((FreshClassActual.classHooksQuietB_eq hc hm.sat hd).trans hmain.classHooks)
    (FreshClassActual.chainsIn hc hd hel)
    ((FreshClassActual.classPayload_live hd hol).trans hmain.classLive) hmain.phase hmain.origin
    hrun
  exact RunSpec.step (answerPoint_evalFrom _ _) hs (hcb.rebase (Framed_reCtl m _ []))

#print axioms class_actual_runSpec
end Ratchet.Denote.Typed
