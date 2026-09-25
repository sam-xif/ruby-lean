import Denote.Sem.Singleton.SingletonScope
import Denote.Rules.Method.MethodState
import Ratchet.Guards.SingletonCtx

/-! Full singleton body entry, with class-valued self and distinct lexical/dispatch owners. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem singleton_required_scope {m : Machine} {cn name : String} {k e : ObjId}
    {md : MethodDef} (names : List String) (args : List Value)
    (hk : classNamed? m.heap cn = some k) (hl : k < m.heap.objs.size)
    (he : (m.heap.get k).eigen = some e) (code : SingletonMethodCode k e md)
    (hp : m.preludeMode = false) :
    SingletonScopeAt cn k e (pushMethodFrame m (requiredFrame (.ref k) name md names args)) := by
  refine ⟨hk, hl, he, ?_, ?_, ?_, ?_, hp⟩
  · rw [currentFrame_pushMethodFrame]; rfl
  · rw [currentFrame_pushMethodFrame]; exact code.owner
  · rw [currentFrame_pushMethodFrame]; exact code.cref
  · rw [currentFrame_pushMethodFrame]; rfl

theorem singleton_pop_scope {m n : Machine} {cn : String} {k e : ObjId} {f : RubyCore.Frame}
    (scope : SingletonScopeAt cn k e m) (hl : FrameInRange m)
    (hc : f.captured = none) (h : Framed (pushMethodFrame m f) n)
    (hp : n.preludeMode = false) : SingletonScopeAt cn k e (popMethodFrame n) :=
  scope.framed (method_pop_framed hl.2 hc h) hl.1 hp

theorem singleton_enter_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cn name : String} {k e : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (site : InstanceSite κ cn k m.heap) (he : (m.heap.get k).eigen = some e)
    (code : SingletonMethodCode k e md) (hp : m.preludeMode = false)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (singletonBodyCtx κ cn name) x = constGet? κ x) :
    StateOk (singletonBodyCtx κ cn name) ps .ivar0
      (pushMethodFrame m (requiredFrame (.ref k) name md (ps.map (·.1)) args)) := by
  let entry := pushMethodFrame m (requiredFrame (.ref k) name md (ps.map (·.1)) args)
  have scope := singleton_required_scope (name := name) (ps.map (·.1)) args site.named site.live he code hp
  have hscope : ConstScopeOk entry := scope.constScope site
  have hden (τ : Ty) (hτ : FirstOrder τ = true) (v : Value) :
      denM τ m v → denM τ entry v :=
    (denM_heap_only (m₁ := m) (m₂ := entry) hτ rfl).mp
  have hself : denM (.clsOf cn) entry entry.currentFrame.self := by
    rw [scope.self, denM]
    change isClassRefNamed m.heap (.ref k) cn = true
    simp only [isClassRefNamed, site.named, beq_self_eq_true]
  refine {
    runtime := by intro h; cases h
    mainSite := hm.mainSite
    moduleBase := hm.moduleBase
    allocators := hm.allocators
    globalConsts := hm.globalConsts
    classRuntime := by intro q h; cases h
    singletonRuntime := by
      intro q hq
      change some cn = some q at hq
      cases hq
      exact ⟨k, e, scope⟩
    classSites := by
      intro q hq
      apply hm.classSites q
      exact List.mem_append_left _ (by simpa only [classSiteNames, singletonBodyCtx,
        Option.toList_none, List.append_nil] using hq)
    sat := hm.sat
    primitiveDispatch := hm.primitiveDispatch
    primitiveErrors := hm.primitiveErrors
    stringPayload := hm.stringPayload
    arrayPayload := hm.arrayPayload
    hashPayload := hm.hashPayload
    core := hm.core
    frameInRange := by simp [FrameInRange, pushMethodFrame]
    env := requiredFrame_envOk m (.ref k) name md ps args hlen hargs hps
    selfSpine := ⟨by simp [denSpine, denSpineFrom], by intro _ _ hc; cases hc⟩
    classes := hm.classes
    ownNames := hm.ownNames
    classChains := hm.classChains
    rootInit := hm.rootInit
    defs := hm.defs
    asms := by intro a ham; change a ∈ κ.asms at ham; rw [ha] at ham; cases ham
    frame := ⟨by rw [currentFrame_pushMethodFrame]; simp only [requiredFrame, code.superName, Option.getD_none],
      hself, by rw [currentFrame_pushMethodFrame]; rfl⟩
    closures := trivial
    blockTy := by change entry.currentFrame.blk = none; rw [currentFrame_pushMethodFrame]; rfl
    selfTy := hself
    consts := ?_
    constPaths := fun owner x τ j hx hj v hv =>
      hden τ (ht.paths _ τ hx) v (hm.constPaths owner x τ j hx hj v hv)
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
    selfLive := by intro j hj; rw [scope.self] at hj; cases hj; exact site.live }
  · intro x τ hx
    obtain ⟨v, hv, hd⟩ := hm.consts x τ (by rwa [hk] at hx)
    exact ⟨v, (hscope x).trans ((hm.constScope x).symm.trans hv), hden τ (ht.consts x τ (by rwa [hk] at hx)) v hd⟩
  · intro name hn j hj owner found hmd
    rw [nameFreeSites, currentFrame_pushMethodFrame] at hj
    rcases List.mem_cons.mp hj with hj | hj
    · rw [hj] at hmd
      exact site.classNames name hn owner found hmd
    · exact hm.nameFree name hn j (List.mem_cons_of_mem _ hj) owner found hmd

theorem singleton_enterUserMethod_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cn name : String} {k e : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (site : InstanceSite κ cn k m.heap) (he : (m.heap.get k).eigen = some e)
    (code : SingletonMethodCode k e md) (hp : m.preludeMode = false)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (singletonBodyCtx κ cn name) x = constGet? κ x)
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req) :
    ∃ n, Interp.enterUserMethod m (.ref k) name md args none = .next n ∧
      n.ctl = .eval md.body ∧ StateOk (singletonBodyCtx κ cn name) ps .ivar0 n := by
  have hs := singleton_enter_state hm ht ha site he code hp hlen hargs hps hk
  refine ⟨_, enterUserMethod_required m (.ref k) name md _ args hparams code.captured code.declared
    (by simpa using hlen), rfl, StateOk_reCtl hs _ _⟩

#print axioms singleton_required_scope
#print axioms singleton_pop_scope
#print axioms singleton_enter_state
#print axioms singleton_enterUserMethod_state
end Ratchet.Denote.Typed
