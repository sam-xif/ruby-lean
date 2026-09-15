import Denote.Typed.InstanceState
import Denote.Sem.FramedNames

/-! Restore an instance caller, independently of the callee's receiver and lexical class.
Post-call sites supply heap facts; saved frames and first-order framing supply caller data. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem restore_instance_state {κ κb : Ctx} {Γ Γb : Env} {I Ib Is : Ty} {m n : Machine}
    {ownerName recvName : String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = false) (hcl : κ.scope.runtimeClass = some ownerName)
    (hself : κ.selfTy = some (.inst recvName Is))
    (ho : ownerName ∈ κb.classes.map (·.name)) (hv : recvName ∈ κb.classes.map (·.name))
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hp : Framed m (popMethodFrame n)) (hpop : (popMethodFrame n).currentFrame = m.currentFrame)
    (he : EnvOk Γ (popMethodFrame n)) (hphase : n.preludeMode = false)
    (hn : StateOk κb Γb Ib n) : StateOk (returnScopeCtx κ κb) Γ I (popMethodFrame n) := by
  obtain ⟨oldk, old⟩ := hm.classRuntime ownerName hcl
  obtain ⟨k, site⟩ := hn.classSites ownerName (List.mem_append_left _ ho)
  have hid : oldk = k := Option.some.inj ((hp.classNamed old.named).symm.trans site.named)
  subst oldk
  have ready : ClassScopeAt ownerName k (popMethodFrame n) := {
    named := site.named
    live := site.live
    owner := (congrArg RubyCore.Frame.defmod hpop).trans old.owner
    cref := (congrArg RubyCore.Frame.cref hpop).trans old.cref
    captured := (congrArg RubyCore.Frame.captured hpop).trans old.captured
    phase := hphase
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
    exact hp.firstOrder _ (ht.self _ hself) _ (by simpa only [SelfTyOk, hself] using hm.selfTy)
  refine {
    runtime := by intro hh; change κ.scope.runtimeMain = true at hh; rw [hr] at hh; cases hh
    mainSite := hn.mainSite
    allocators := hn.allocators
    globalConsts := hn.globalConsts
    classRuntime := by
      intro cn hcn
      change κ.scope.runtimeClass = some cn at hcn
      have hn : ownerName = cn := Option.some.inj (hcl.symm.trans hcn)
      subst cn
      exact ⟨k, ready⟩
    classSites := by
      intro cn hcn
      apply hn.classSites cn
      apply List.mem_append_left
      change cn ∈ κb.classes.map (·.name)
      change cn ∈ κb.classes.map (·.name) ++ κ.scope.runtimeClass.toList at hcn
      rcases List.mem_append.mp hcn with hcn | hcn
      · exact hcn
      · have he : cn = ownerName := by simpa only [hcl, Option.toList_some, List.mem_singleton] using hcn
        exact he ▸ ho
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
  · change FrameOk κ.frame (popMethodFrame n)
    cases hf : κ.frame with
    | none => simpa only [FrameOk, hf, hpop] using hm.frame
    | some fr =>
      have hold : m.currentFrame.meth = fr.methName ∧ isAName m.heap m.currentFrame.self fr.recvClass = true := by
        simpa only [FrameOk, hf] using hm.frame
      exact ⟨by rw [hpop]; exact hold.1, by rw [hpop]; exact hp.nominal _ _ hold.2⟩
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
      obtain ⟨r, rsite⟩ := hn.classSites recvName (List.mem_append_left _ hv)
      have hd : denM (.inst recvName Is) (popMethodFrame n) (popMethodFrame n).currentFrame.self := by
        simpa only [SelfTyOk, hself] using hself'
      rw [denM] at hd
      have hco := exactInst_classOf hd.1 rsite.named
      exact rsite.names name hb owner md (by rwa [hco] at hl)
    · exact hn.nameFree name hb j (List.mem_cons_of_mem _ hj) owner md hl

theorem instance_pop_instance_state {κ : Ctx} {Γ Γb : Env} {I Ib Is : Ty} {m n : Machine}
    {f : RubyCore.Frame} {fr : Ratchet.Frame} {ownerName recvName : String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = false) (hcl : κ.scope.runtimeClass = some ownerName)
    (hself : κ.selfTy = some (.inst recvName Is))
    (ho : ownerName ∈ κ.classes.map (·.name)) (hv : recvName ∈ κ.classes.map (·.name))
    (hu : RootUncaptured m) (hc : f.captured = none)
    (hk : ∀ x, constGet? (instanceBodyCtx κ fr Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : Framed (pushMethodFrame m f) n)
    (hn : StateOk (instanceBodyCtx κ fr Ib) Γb Ib n) : StateOk κ Γ I (popMethodFrame n) := by
  obtain ⟨_, scope⟩ := hn.classRuntime fr.defClass rfl
  exact restore_instance_state (κb := instanceBodyCtx κ fr Ib) hm ht ha hr hcl hself ho hv hk
    (method_pop_framed hm.frameInRange.2 hc h) (method_pop_currentFrame hm.frameInRange hc h)
    (method_pop_envOk hm.frameInRange.2 hu hc h hm.env hΓ) scope.phase hn

#print axioms restore_instance_state
#print axioms instance_pop_instance_state
end Ratchet.Denote.Typed
