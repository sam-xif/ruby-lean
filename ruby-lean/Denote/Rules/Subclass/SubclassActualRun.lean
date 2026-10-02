import Denote.Sem.Subclass.SubclassActualStep
import Denote.Sem.Class.ClassFreshness
import Denote.Rules.Class.ClassActivation
import Denote.Rules.Class.ClassCallbacks

/-! Fresh subclass execution: registration, Object's const_added, the parent's native
inherited, the published header body and the original class-frame return. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshModFrame)

theorem stepFn_parent_hook {m : Machine} {p owner : ObjId} {cp : ClassPayload} {md : MethodDef}
    {arg : Value} (hpay : (m.heap.get p).payload = .cls cp)
    (hl : lookup m.heap (.ref p) "inherited" = some (owner, md))
    (hb : md.builtin = some "Class#inherited") (hu : md.undefined = false) :
    Interp.stepFn { m with ctl := .send (.ref p) .reflective "inherited" [arg] none [] } =
      .next { m with ctl := .value .nil } ∨
    ∃ msg, Interp.stepFn { m with ctl := .send (.ref p) .reflective "inherited" [arg] none [] } =
      .unsupported msg :=
  invoke_native_class_hook (m := { m with ctl := .send (.ref p) .reflective "inherited" [arg] none [] })
    (by simp [classHookNames]) hpay hl hb hu

theorem subclass_callbacks_runSpec {origin m : Machine} {κ : Ctx} {Γ : Env} {I τ : Ty}
    {k p owner : ObjId} {cp : ClassPayload} {md : MethodDef} {name : String} {body : RubyCore.Expr}
    (hq : classHooksQuietB m.heap = true) (hc : Proof.ChainsIn m.heap)
    (hl : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hpay : (m.heap.get p).payload = .cls cp)
    (hli : lookup m.heap (.ref p) "inherited" = some (owner, md))
    (hib : md.builtin = some "Class#inherited") (hiu : md.undefined = false)
    (hp : m.preludeMode = false) (ho : m.currentFrame.libraryOrigin = false)
    (hb : RunSpec origin (classCallbackBody m k body) Γ τ κ I) :
    RunSpec origin
      { m with
        ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym name] none [],
        kont := .constClassK k (some p) name body :: m.kont } Γ τ κ I := by
  let added := { m with kont := .constClassK k (some p) name body :: m.kont }
  let inherited := { m with kont := .classBodyK k name body :: m.kont }
  obtain hs | ⟨msg, hs⟩ := stepFn_class_hook (m := added) (arg := .sym name)
    (by simp [classHookNames] : ("const_added", "Module#const_added") ∈ classHookNames) hq hc hl
  · apply RunSpec.step (show answerPoint _ = none from rfl) hs
    apply RunSpec.step (show answerPoint _ = none from rfl)
      (show Interp.stepFn { added with ctl := .value .nil } =
        .next { inherited with ctl := .send (.ref p) .reflective "inherited" [.ref k] none [] } from rfl)
    obtain hi | ⟨msg, hi⟩ := stepFn_parent_hook (m := inherited) (arg := .ref k) hpay hli hib hiu
    · apply RunSpec.step (show answerPoint _ = none from rfl) hi
      exact RunSpec.step (show answerPoint _ = none from rfl) (stepFn_classBodyK hp ho) hb
    · exact RunSpec.unsupported (show answerPoint _ = none from rfl) hi
  · exact RunSpec.unsupported (show answerPoint _ = none from rfl) hs

#print axioms subclass_callbacks_runSpec

/-- From the parent value's delivery to `classDefK` through the subclass body and return. -/
theorem subclass_actual_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {c : Cls} {p : ObjId} {name : String} {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none)
    (hw : κb.pos.mainWorld = true) (hcl : κ.scope.runtimeClass = none)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (htables : ClassTablesFrame κ name m) (hnative : FreshClass.nativeFrameB κ name = true)
    (hfresh : freshClassNameB κ name = true) (hne : name.isEmpty = false)
    (hquiet : classNativeQuietB name "new" = true)
    (hplain : unqualifiedClassB name = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some p)
    (halloc : c.name ∈ κ.pos.plainAlloc) (hnew : smroGet? κ.classes c.name "new" = none)
    (hframe : SubclassHeaderFrame κ.classes name c.name)
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true)
    (hb : SemSafeCtxA (subclassHeaderCtx (classBodyCtx κ name) name c.name) [] .ivar0 body τ κb Γb Ib) :
    RunSpec m (deliverA (.val (.ref p)) m [.classDefK name (toRuby body)]) Γ τ
      (returnScopeCtx κ κb) I := by
  have hn := hm.freshClassName hfresh
  have hmain := hm.runtime hr
  have hcr := hm.core.classReady
  have hch := hcr.chains
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hol := lt_size_of_classPayload hmain.classLive
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hol
  have site := hm.classSites.at_class hc hp
  have hpl := site.live
  have hkind := hm.ordinary_decl hc halloc
  obtain ⟨e, he, _, _⟩ := site.metaAttached
  have hel := hch.eigen _ hpl _ he
  have hpf := FreshClassActual.ParentFacts.of_declared hm hc hp he hkind
  have hmod := (hm.declCls c hc p hp).2.2.2.1
  rw [hkind] at hmod
  obtain ⟨cp, hcp⟩ : ∃ cp, m.heap.classPayload? p = some cp := by
    cases hq : m.heap.classPayload? p with
    | none => rw [hq] at hmod; cases hmod
    | some cp => exact ⟨cp, rfl⟩
  have hcpm : cp.isModule = false := by rw [hcp] at hmod; simpa using hmod
  have hat : cp.attached = none := by simpa [hcp] using site.detached
  have hcls : p ≠ Boot.classId := by
    intro h; subst h; exact absurd site.afterBuiltins (by decide)
  have hpay : (m.heap.get p).payload = .cls cp := by
    unfold Heap.classPayload? at hcp; split at hcp <;> simp_all
  have hs := FreshClassActual.stepFn_subclass (body := toRuby body) hmain hn hcp hcpm hat hcls hpl he
  let st := reCtl m (.value (.ref p)) []
  have hst : StateOk κ Γ I st := StateOk_reCtl hm _ []
  have hheader := FreshClassActual.headerSub (body := toRuby body) hst hr hf ha
    (htables.heap rfl) (FreshClass.nativeFrameB_sound hnative) hn hne hc hp halloc he hreach hquiet hplain
    hframe hnew
  have hbody := hb _ (StateOk_reCtl hheader (.eval (toRuby body)) [])
  obtain ⟨ep, he', hbasic, _⟩ := hpf.metaReady
  rw [he] at he'; cases he'
  let pub := ClassActivation.publishHeap st (FreshClassActual.heap m name e p)
  have hfr : Framed st pub :=
    FreshClassActual.framed hst htop hn hel hbasic rfl rfl (.of_eq rfl rfl)
  have hrun := ClassActivation.runSpec (k := m.heap.objs.size) hst hfr ht ha hr hw hcl hq hk hΓ hτ
    (hbody.rebase (Framed.of_heap_stack rfl rfl (.of_eq rfl rfl)))
  have hli : lookup (FreshClassActual.heap m name e p) (.ref p) "inherited" =
      lookup m.heap (.ref p) "inherited" := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, FreshClassActual.classOf_old hd hpl,
      FreshClassActual.method_old hch hm.sat hd (Proof.ClsGrow.classOf_lt hch hpl)]
  have hinh := hpf.inheritedHook
  cases hl : lookup m.heap (.ref p) "inherited" with
  | none => rw [hl] at hinh; cases hinh
  | some r =>
  obtain ⟨owner, md⟩ := r
  rw [hl] at hinh
  simp only [Option.any_some, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hinh
  have hpay' : ((FreshClassActual.heap m name e p).get p).payload = .cls cp := by
    rw [FreshClassActual.get_old hd hpl,
      RubyCore.Proof.Static.get_constSetIn_ne _ _ _ _ _ (by rw [htop]; exact fun h => absurd (h ▸ site.afterBuiltins) (by decide))]
    exact hpay
  have hcb := subclass_callbacks_runSpec (m := { st with heap := FreshClassActual.heap m name e p })
    (k := m.heap.objs.size) (name := name) (body := toRuby body)
    ((FreshClassActual.classHooksQuietB_eq hch hm.sat hd).trans hmain.classHooks)
    (FreshClassActual.chainsIn hch hd hel hpl)
    ((FreshClassActual.classPayload_live hd hol).trans hmain.classLive) hpay' (hli.trans hl)
    hinh.2 hinh.1 hmain.phase hmain.origin hrun
  exact RunSpec.step (show answerPoint _ = none from rfl) hs (hcb.rebase (Framed_reCtl m _ []))

#print axioms subclass_actual_runSpec
end Ratchet.Denote.Typed
