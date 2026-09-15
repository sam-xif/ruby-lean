import Denote.Typed.InstanceResolve
import Denote.Sem.ClassCore

/-! Full annotated instance-body entry. Unlike top-level method entry, self, block,
lexical scope, and the ivar spine can all change. Receiver and lexical owner have independent
sites: receiver facts type self, owner facts justify scope. No inherited lookup is inferred. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem instance_enter_state_at {κ : Ctx} {Γ : Env} {I Ib : Ty} {m : Machine}
    {cn ownerCn name : String} {r k : ObjId} {md : MethodDef} {recv : Value}
    {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (site : InstanceSite κ cn r m.heap) (owner : InstanceSite κ ownerCn k m.heap)
    (hp : m.preludeMode = false)
    (code : InstanceMethodCode k name md) (hi : FirstOrder Ib = true)
    (hv : denM (.inst cn Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨cn, ownerCn, name⟩ Ib) x = constGet? κ x) :
    StateOk (instanceBodyCtx κ ⟨cn, ownerCn, name⟩ Ib) ps Ib
      (pushMethodFrame m (requiredFrame recv name md (ps.map (·.1)) args)) := by
  let entry := pushMethodFrame m (requiredFrame recv name md (ps.map (·.1)) args)
  have hscope : ConstScopeOk entry :=
    InstanceSite.constScope (m := entry) owner (by rw [currentFrame_pushMethodFrame]; exact code.cref)
      (by rw [currentFrame_pushMethodFrame]; exact code.owner)
  have hresolve (x : String) : constResolveAt entry x = constResolveAt m x :=
    (hscope x).trans (hm.constScope x).symm
  have hden (τ : Ty) (hτ : FirstOrder τ = true) (v : Value) :
      denM τ m v → denM τ entry v :=
    (denM_heap_only (m₁ := m) (m₂ := entry) hτ rfl).mp
  have hco : classOf m.heap recv = r := by
    rw [denM] at hv
    exact exactInst_classOf hv.1 site.named
  refine {
    runtime := by intro h; cases h
    mainSite := hm.mainSite
    allocators := hm.allocators
    globalConsts := hm.globalConsts
    classRuntime := ?_
    classSites := by
      intro q hq
      change q ∈ κ.classes.map (·.name) ++ [ownerCn] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hm.classSites q (List.mem_append_left _ hq)
      · have hq := List.mem_singleton.mp hq
        subst q
        exact ⟨k, owner⟩
    sat := hm.sat
    primitiveDispatch := hm.primitiveDispatch
    primitiveErrors := hm.primitiveErrors
    stringPayload := hm.stringPayload
    arrayPayload := hm.arrayPayload
    hashPayload := hm.hashPayload
    core := hm.core
    frameInRange := by simp [FrameInRange, pushMethodFrame]
    env := requiredFrame_envOk m recv name md ps args hlen hargs hps
    selfSpine := instance_required_spine md _ _ hi hv
    classes := hm.classes
    ownNames := hm.ownNames
    classChains := hm.classChains
    defs := hm.defs
    asms := by intro a ham; change a ∈ κ.asms at ham; rw [ha] at ham; cases ham
    frame := instance_required_frame_at _ _ site.named hv site.front code
    closures := trivial
    blockTy := by change entry.currentFrame.blk = none; rw [currentFrame_pushMethodFrame]; rfl
    selfTy := instance_required_self md _ _ hi hv
    consts := ?_
    constPaths := ?_
    nested := hm.nested
    privConsts := hm.privConsts
    constScope := hscope
    exact := hm.exact
    nameFree := ?_
    bareFree := by intro _ _ _ hself; cases hself
    missFree := by intro _ hself; cases hself
    query := hm.query
    clsQuery := hm.clsQuery
    declCls := hm.declCls
    baseChains := hm.baseChains
    nilQuery := hm.nilQuery
    selfLive := instance_required_live md _ _ site.named hv }
  · intro cn' hr
    change some ownerCn = some cn' at hr
    cases hr
    exact ⟨k, instance_required_scope _ _ owner.named owner.live code hp owner.hook⟩
  · intro x τ hx
    rw [hk] at hx
    obtain ⟨v, hv, htau⟩ := hm.consts x τ hx
    exact ⟨v, (hresolve x).trans hv, hden τ (ht.consts x τ hx) v htau⟩
  · intro owner x τ j hx hj v hv
    exact hden τ (ht.paths _ τ hx) v (hm.constPaths owner x τ j hx hj v hv)
  · intro n hn j hj owner found hmd
    rw [nameFreeSites, currentFrame_pushMethodFrame] at hj
    change j ∈ [classOf m.heap recv, classOf m.heap (.ref Boot.objectId), Boot.objectId] at hj
    rcases List.mem_cons.mp hj with hj | hj
    · rw [hj, hco] at hmd
      exact site.names n hn owner found hmd
    · exact hm.nameFree n hn j (List.mem_cons_of_mem _ hj) owner found hmd

/-- The own-method entry is the specialization where receiver and lexical owner coincide. -/
theorem instance_enter_state {κ : Ctx} {Γ : Env} {I Ib : Ty} {m : Machine}
    {cn name : String} {k : ObjId} {md : MethodDef} {recv : Value}
    {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (site : InstanceSite κ cn k m.heap) (hp : m.preludeMode = false)
    (code : InstanceMethodCode k name md) (hi : FirstOrder Ib = true)
    (hv : denM (.inst cn Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨cn, cn, name⟩ Ib) x = constGet? κ x) :
    StateOk (instanceBodyCtx κ ⟨cn, cn, name⟩ Ib) ps Ib
      (pushMethodFrame m (requiredFrame recv name md (ps.map (·.1)) args)) :=
  instance_enter_state_at hm ht ha site site hp code hi hv hlen hargs hps hk

/-- Bind the checked parameter domain through the real interpreter entry. Control and
continuation are retained exactly; applying the body and restoring the caller are separate. -/
theorem instance_enterUserMethod_state_at {κ : Ctx} {Γ : Env} {I Ib : Ty} {m : Machine}
    {cn ownerCn name : String} {r k : ObjId} {md : MethodDef} {recv : Value}
    {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (site : InstanceSite κ cn r m.heap) (owner : InstanceSite κ ownerCn k m.heap)
    (hp : m.preludeMode = false)
    (code : InstanceMethodCode k name md) (hi : FirstOrder Ib = true)
    (hv : denM (.inst cn Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨cn, ownerCn, name⟩ Ib) x = constGet? κ x)
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req) :
    ∃ n, Interp.enterUserMethod m recv name md args none = .next n ∧
      n.ctl = .eval md.body ∧
      StateOk (instanceBodyCtx κ ⟨cn, ownerCn, name⟩ Ib) ps Ib n := by
  have he := instance_enter_state_at hm ht ha site owner hp code hi hv hlen hargs hps hk
  refine ⟨_, enterUserMethod_required m recv name md _ args hparams code.captured code.declared
    (by simpa using hlen), rfl, ?_⟩
  exact StateOk_reCtl he _ _

theorem instance_enterUserMethod_state {κ : Ctx} {Γ : Env} {I Ib : Ty} {m : Machine}
    {cn name : String} {k : ObjId} {md : MethodDef} {recv : Value}
    {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (site : InstanceSite κ cn k m.heap) (hp : m.preludeMode = false)
    (code : InstanceMethodCode k name md) (hi : FirstOrder Ib = true)
    (hv : denM (.inst cn Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨cn, cn, name⟩ Ib) x = constGet? κ x)
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req) :
    ∃ n, Interp.enterUserMethod m recv name md args none = .next n ∧
      n.ctl = .eval md.body ∧
      StateOk (instanceBodyCtx κ ⟨cn, cn, name⟩ Ib) ps Ib n :=
  instance_enterUserMethod_state_at hm ht ha site site hp code hi hv hlen hargs hps hk hparams

#print axioms instance_enter_state
#print axioms instance_enterUserMethod_state
#print axioms instance_enter_state_at
#print axioms instance_enterUserMethod_state_at
end Ratchet.Denote.Typed
