import Denote.Rules.Instance.InstanceState
import Denote.Rules.Init.InitNestedReturn

/-! Nested initialization keeps the same fresh receiver and allocation anchor. Entry
changes lexical owner and parameters; return restores locals and retains the new fields. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem super_initializer_state {anchor : Heap} {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cn ownerCn : String} {r k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    (hm : InitState anchor κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (site : InstanceSite κ cn r m.heap) (owner : InstanceSite κ ownerCn k m.heap)
    (hp : m.preludeMode = false) (code : InstanceMethodCode k "initialize" md)
    (hself : κ.selfTy = some (.inst cn .ivar0)) (hclosed : κ.scope.closedIvars = true)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (initializerBodyCtxAt κ cn ownerCn) x = constGet? κ x) :
    InitState anchor (initializerBodyCtxAt κ cn ownerCn) ps I
      (pushMethodFrame m (requiredFrame m.currentFrame.self "initialize" md (ps.map (·.1)) args)) := by
  let entry := pushMethodFrame m (requiredFrame m.currentFrame.self "initialize" md (ps.map (·.1)) args)
  have hv : denM (.inst cn .ivar0) m m.currentFrame.self := by
    simpa only [SelfTyOk, hself] using hm.typed.selfTy
  have he := instance_enter_state_at hm.typed ht ha site owner hp code rfl hv hlen hargs hps hk
  refine ⟨{ he with selfSpine := ?_ }, hm.growth, ?_⟩
  · change denSpine I entry _ ∧ _
    have hs : entry.currentFrame.self = m.currentFrame.self := by
      simp only [entry, currentFrame_pushMethodFrame, requiredFrame]
    rw [hs]
    exact ⟨((denM_heap_only_aux I ht.spine).2 m entry _ [] rfl).mp hm.typed.selfSpine.1,
      fun x hx _ => hm.typed.selfSpine.2 x hx hclosed⟩
  · obtain ⟨o, hs, ha, hl, hf⟩ := hm.fresh
    exact ⟨o, by simpa only [currentFrame_pushMethodFrame, requiredFrame] using hs, ha, hl, hf⟩

/-- Restore an initializer caller with the callee's output spine. Ordinary Framed is
too strong here: the receiver existed at nested entry and its fields have just changed. -/
theorem super_initializer_pop_state {anchor : Heap} {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty}
    {m n : Machine} {f : RubyCore.Frame} {ownerName recvName bodyOwner : String}
    (hm : InitState anchor κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) Ib)
    (ha : κ.asms = []) (hr : κ.scope.runtimeMain = false)
    (hcl : κ.scope.runtimeClass = some ownerName) (hq : κb.scope.runtimeClass = some bodyOwner)
    (hself : κ.selfTy = some (.inst recvName .ivar0)) (hblock : κ.blockTy = none)
    (hclosed : κ.scope.closedIvars = κb.scope.closedIvars)
    (ho : ownerName ∈ κb.classes.map (·.name)) (hv : recvName ∈ κb.classes.map (·.name))
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, IvarStable (stripAlias p.2) = true)
    (hc : f.captured = none) (hs : f.self = m.currentFrame.self)
    (h : InitFrame anchor (pushMethodFrame m f) n) (hn : InitState anchor κb Γb Ib n) :
    InitState anchor (returnScopeCtx κ κb) Γ Ib (popMethodFrame n) := by
  have hp := h.pop hm.typed.frameInRange.2 hc
  have hpop := h.pop_currentFrame hm.typed.frameInRange hc
  have hsame : (popMethodFrame n).currentFrame.self = n.currentFrame.self := by
    rw [hpop, h.body_self, hs]
  obtain ⟨oldk, old⟩ := hm.typed.classRuntime ownerName hcl
  obtain ⟨k, site⟩ := hn.typed.classSites ownerName (List.mem_append_left _ ho)
  have hnamed : classNamed? n.heap ownerName = classNamed? m.heap ownerName :=
    (hn.growth.classNamed?_eq _).trans (hm.growth.classNamed?_eq _).symm
  have hid : oldk = k := Option.some.inj ((hnamed.trans old.named).symm.trans site.named)
  subst oldk
  obtain ⟨_, bodyScope⟩ := hn.typed.classRuntime bodyOwner hq
  have ready : ClassScopeAt ownerName k (popMethodFrame n) := {
    named := site.named
    live := site.live
    owner := (congrArg RubyCore.Frame.defmod hpop).trans old.owner
    cref := (congrArg RubyCore.Frame.cref hpop).trans old.cref
    captured := (congrArg RubyCore.Frame.captured hpop).trans old.captured
    phase := bodyScope.phase
    visibility := by simpa only [defaultDefVis, hpop] using old.visibility
    hook := site.hook }
  have hscope : ConstScopeOk (popMethodFrame n) :=
    InstanceSite.constScope (m := popMethodFrame n) site ready.cref ready.owner
  have hden (τ : Ty) (hτ : FirstOrder τ = true) (v : Value) :
      denM τ n v → denM τ (popMethodFrame n) v :=
    (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) hτ rfl).mp
  have hself' : SelfTyOk κ.selfTy (popMethodFrame n) := by
    simp only [SelfTyOk, hself]
    rw [hpop]
    exact hp.stable _ rfl _ (by simpa only [SelfTyOk, hself] using hm.typed.selfTy)
  refine ⟨?_, hn.growth, ?_⟩
  · refine {
      runtime := by intro hh; change κ.scope.runtimeMain = true at hh; rw [hr] at hh; cases hh
      mainSite := hn.typed.mainSite
      moduleBase := hn.typed.moduleBase
      allocators := hn.typed.allocators
      globalConsts := hn.typed.globalConsts
      classRuntime := by
        intro cn hcn
        change κ.scope.runtimeClass = some cn at hcn
        have he : ownerName = cn := Option.some.inj (hcl.symm.trans hcn)
        subst cn
        exact ⟨k, ready⟩
      singletonRuntime := by
        intro cn hr
        obtain ⟨_, _, scope⟩ := hm.typed.singletonRuntime cn hr
        exact False.elim (scope.not_instance (by simpa only [SelfTyOk, hself] using hm.typed.selfTy))
      classSites := by
        intro cn hcn
        apply hn.typed.classSites cn
        apply List.mem_append_left
        change cn ∈ κb.classes.map (·.name) ++ κ.scope.runtimeClass.toList at hcn
        rcases List.mem_append.mp hcn with hcn | hcn
        · exact hcn
        · have he : cn = ownerName := by simpa only [hcl, Option.toList_some, List.mem_singleton] using hcn
          exact he ▸ ho
      sat := hn.typed.sat
      primitiveDispatch := hn.typed.primitiveDispatch
      primitiveErrors := hn.typed.primitiveErrors
      stringPayload := hn.typed.stringPayload
      arrayPayload := hn.typed.arrayPayload
      hashPayload := hn.typed.hashPayload
      frozenFields := hn.typed.frozenFields
      core := hn.typed.core
      frameInRange := ⟨by rw [hp.stack]; exact hm.typed.frameInRange.1,
        by rw [hp.stack]; exact Nat.lt_of_lt_of_le hm.typed.frameInRange.2 hp.frames.size⟩
      env := h.pop_env hm.typed.frameInRange (by
        rw [RootUncaptured, rootFrame_eq_currentFrame hm.typed.frameInRange.1]; exact old.captured)
        hc hm.typed.env hΓ hm.typed.localAlias
      selfSpine := ?_
      classes := hn.typed.classes
      ownNames := hn.typed.ownNames
      classChains := hn.typed.classChains
      rootInit := hn.typed.rootInit
      defs := hn.typed.defs
      asms := by change AsmsOk κ.asms _; simp [AsmsOk, ha]
      frame := ?_
      closures := trivial
      blockTy := by
        change BlockTyOk κ.blockTy (popMethodFrame n)
        simpa only [BlockTyOk, hblock, hpop] using hm.typed.blockTy
      selfTy := hself'
      consts := ?_
      constPaths := fun owner x τ j hx hj v hw => hden τ (ht.paths _ τ hx) v
        (hn.typed.constPaths owner x τ j hx hj v hw)
      nested := hn.typed.nested
      privConsts := trivial
      constScope := hscope
      exact := hn.typed.exact
      nameFree := ?_
      bareFree := by intro _ _ _ hh; change κ.selfTy = none at hh; rw [hself] at hh; cases hh
      missFree := by intro _ hh; change κ.selfTy = none at hh; rw [hself] at hh; cases hh
      query := hn.typed.query
      clsQuery := hn.typed.clsQuery
      declCls := hn.typed.declCls
      baseChains := hn.typed.baseChains
      nilQuery := hn.typed.nilQuery
      selfLive := fun o ho => hn.typed.selfLive o (hsame.symm.trans ho) }
    · change denSpine Ib (popMethodFrame n) _ ∧ _
      rw [hsame]
      exact ⟨((denM_heap_only_aux Ib ht.spine).2 n (popMethodFrame n) _ [] rfl).mp hn.typed.selfSpine.1,
        fun x hx hh => hn.typed.selfSpine.2 x hx (hclosed ▸ hh)⟩
    · change FrameOk κ.frame (popMethodFrame n)
      cases hf : κ.frame with
      | none => simpa only [FrameOk, hf, hpop] using hm.typed.frame
      | some fr =>
        have hold := hm.typed.frame
        simp only [FrameOk, hf] at hold
        exact ⟨by rw [hpop]; exact hold.1,
          by
            rw [hpop]
            simpa only [denM] using hp.stable fr.recvTy (by unfold Frame.recvTy; split <;> rfl) m.currentFrame.self hold.2.1,
          by rw [hpop]; exact hold.2.2⟩
    · intro x τ hx
      obtain ⟨v, hw, hd⟩ := hn.typed.consts x τ (by rwa [hk])
      exact ⟨v, (hscope x).trans ((hn.typed.constScope x).symm.trans hw), hden τ (ht.consts x τ hx) v hd⟩
    · intro name hb j hmem owner md hl
      change j ∈ classOf (popMethodFrame n).heap (popMethodFrame n).currentFrame.self :: _ at hmem
      rcases List.mem_cons.mp hmem with hj | hj
      · subst j
        obtain ⟨r, rsite⟩ := hn.typed.classSites recvName (List.mem_append_left _ hv)
        have hd : denM (.inst recvName .ivar0) (popMethodFrame n) (popMethodFrame n).currentFrame.self := by
          simpa only [SelfTyOk, hself] using hself'
        rw [denM] at hd
        exact rsite.names name hb owner md (by rwa [exactInst_classOf hd.1 rsite.named] at hl)
      · exact hn.typed.nameFree name hb j (List.mem_cons_of_mem _ hj) owner md hl
  · obtain ⟨o, ho, ha, hl, hf⟩ := hn.fresh
    exact ⟨o, hsame.trans ho, ha, hl, hf⟩

#print axioms super_initializer_state
#print axioms super_initializer_pop_state
end Ratchet.Denote.Typed
