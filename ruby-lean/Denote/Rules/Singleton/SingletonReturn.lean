import Denote.Rules.Singleton.SingletonEntry
import Denote.Rules.Instance.InstanceCallerReturn

/-! Restore a singleton caller from saved frame data and the callee's outgoing heap facts. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem restore_singleton_state {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    {cn : String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = false) (hcl : κ.scope.runtimeClass = none)
    (hsg : κ.scope.runtimeSingleton = some cn) (hself : κ.selfTy = some (.clsOf cn))
    (ho : cn ∈ κb.classes.map (·.name))
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hp : Framed m (popMethodFrame n)) (hpop : (popMethodFrame n).currentFrame = m.currentFrame)
    (he : EnvOk Γ (popMethodFrame n)) (hphase : n.preludeMode = false)
    (hn : StateOk κb Γb Ib n) : StateOk (returnScopeCtx κ κb) Γ I (popMethodFrame n) := by
  obtain ⟨oldk, e, old⟩ := hm.singletonRuntime cn hsg
  obtain ⟨k, site⟩ := hn.classSites cn (List.mem_append_left _ ho)
  have hid : oldk = k := Option.some.inj ((hp.classNamed old.named).symm.trans site.named)
  subst oldk
  have ready := old.framed hp hm.frameInRange.1 hphase
  have hscope : ConstScopeOk (popMethodFrame n) := ready.constScope site
  have hden (τ : Ty) (hτ : FirstOrder τ = true) (v : Value) :
      denM τ n v → denM τ (popMethodFrame n) v :=
    (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) hτ rfl).mp
  have hself' : SelfTyOk κ.selfTy (popMethodFrame n) := by
    simp only [SelfTyOk, hself]
    rw [hpop]
    exact hp.firstOrder _ (ht.self _ hself) _ (by simpa only [SelfTyOk, hself] using hm.selfTy)
  refine {
    runtime := by intro hh; change κ.scope.runtimeMain = true at hh; rw [hr] at hh; cases hh
    mainSite := hn.mainSite
    allocators := hn.allocators
    globalConsts := hn.globalConsts
    classRuntime := by
      intro q hq
      change κ.scope.runtimeClass = some q at hq
      rw [hcl] at hq; cases hq
    singletonRuntime := by
      intro q hq
      change κ.scope.runtimeSingleton = some q at hq
      have heq : cn = q := Option.some.inj (hsg.symm.trans hq)
      subst q
      exact ⟨k, e, ready⟩
    classSites := by
      intro q hq
      apply hn.classSites q
      apply List.mem_append_left
      change q ∈ κb.classes.map (·.name) ++ κ.scope.runtimeClass.toList at hq
      simpa only [hcl, Option.toList_none, List.append_nil] using hq
    sat := hn.sat
    primitiveDispatch := hn.primitiveDispatch
    primitiveErrors := hn.primitiveErrors
    stringPayload := hn.stringPayload
    arrayPayload := hn.arrayPayload
    hashPayload := hn.hashPayload
    core := hn.core
    frameInRange := ⟨by rw [hp.stack]; exact hm.frameInRange.1,
      by rw [hp.stack]; exact Nat.lt_of_lt_of_le hm.frameInRange.2 hp.frames.size⟩
    env := he
    selfSpine := hp.selfSpine (congrArg RubyCore.Frame.self hpop) hm.selfLive ht.spine hm.selfSpine
    classes := hn.classes
    ownNames := hn.ownNames
    classChains := hn.classChains
    rootInit := hn.rootInit
    defs := hn.defs
    asms := by change AsmsOk κ.asms _; simp [AsmsOk, ha]
    frame := ?_
    closures := trivial
    blockTy := ?_
    selfTy := hself'
    consts := ?_
    constPaths := fun owner x τ k hx hk v hv => hden τ (ht.paths _ τ hx) v
      (hn.constPaths owner x τ k hx hk v hv)
    nested := hn.nested
    privConsts := trivial
    constScope := hscope
    exact := hn.exact
    nameFree := ?_
    bareFree := by intro _ _ _ hs; change κ.selfTy = none at hs; rw [hself] at hs; cases hs
    missFree := by intro _ hs; change κ.selfTy = none at hs; rw [hself] at hs; cases hs
    query := hn.query
    clsQuery := hn.clsQuery
    declCls := hn.declCls
    baseChains := hn.baseChains
    nilQuery := hn.nilQuery
    selfLive := fun o ho => Nat.lt_of_lt_of_le (hm.selfLive o (by rwa [hpop] at ho)) hp.fields.size }
  · exact hp.frameOk hm.frame hpop
  · change BlockTyOk κ.blockTy (popMethodFrame n)
    cases hb : κ.blockTy with
    | none => simpa only [BlockTyOk, hb, hpop] using hm.blockTy
    | some τ =>
      obtain ⟨v, hv, hd⟩ := (show ∃ v, m.currentFrame.blk = some v ∧ denM τ m v by
        simpa only [BlockTyOk, hb] using hm.blockTy)
      exact ⟨v, by rw [hpop]; exact hv, hp.firstOrder τ (ht.block τ hb) v hd⟩
  · intro x τ hx
    obtain ⟨v, hv, hd⟩ := hn.consts x τ (by rwa [hk])
    exact ⟨v, (hscope x).trans ((hn.constScope x).symm.trans hv), hden τ (ht.consts x τ hx) v hd⟩
  · intro name hb j hmem owner md hl
    change j ∈ classOf (popMethodFrame n).heap (popMethodFrame n).currentFrame.self :: _ at hmem
    rcases List.mem_cons.mp hmem with hj | hj
    · subst j
      rw [ready.self] at hl
      exact site.classNames name hb owner md hl
    · exact hn.nameFree name hb j (List.mem_cons_of_mem _ hj) owner md hl


theorem instance_pop_singleton_state {κ : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    {f : RubyCore.Frame} {fr : Ratchet.Frame} {cn : String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = false) (hcl : κ.scope.runtimeClass = none)
    (hsg : κ.scope.runtimeSingleton = some cn) (hs : κ.selfTy = some (.clsOf cn))
    (ho : cn ∈ κ.classes.map (·.name)) (hu : RootUncaptured m) (hc : f.captured = none)
    (hk : ∀ x, constGet? (instanceBodyCtx κ fr Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : Framed (pushMethodFrame m f) n)
    (hn : StateOk (instanceBodyCtx κ fr Ib) Γb Ib n) : StateOk κ Γ I (popMethodFrame n) := by
  obtain ⟨_, scope⟩ := hn.classRuntime fr.defClass rfl
  exact restore_singleton_state (κb := instanceBodyCtx κ fr Ib) hm ht ha hr hcl hsg hs ho hk
    (method_pop_framed hm.frameInRange.2 hc h) (method_pop_currentFrame hm.frameInRange hc h)
    (method_pop_envOk hm.frameInRange.2 hu hc h hm.env hΓ) scope.phase hn

#print axioms restore_singleton_state
#print axioms instance_pop_singleton_state
end Ratchet.Denote.Typed
