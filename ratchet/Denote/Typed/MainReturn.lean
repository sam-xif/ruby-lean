import Denote.Typed.InstanceReturn
import Ratchet.ClassCtx

/-! Full top-level caller conformance after an annotation-checked instance body.
The caller's frame/types and the retained heap world are separate proof inputs. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem instance_pop_main_state {κ : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    {f : RubyCore.Frame} {fr : Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κ.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hu : RootUncaptured m) (hc : f.captured = none)
    (hk : ∀ x, constGet? (instanceBodyCtx κ fr Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : Framed (pushMethodFrame m f) n)
    (hn : StateOk (instanceBodyCtx κ fr Ib) Γb Ib n) : StateOk κ Γ I (popMethodFrame n) := by
  have hp := method_pop_framed hm.frameInRange.2 hc h
  have hpop := method_pop_currentFrame hm.frameInRange hc h
  have old := hm.runtime hr
  have site : MainSite κ n.heap := hn.mainSite hw
  obtain ⟨_, scope⟩ := hn.classRuntime fr.defClass rfl
  have ready : MainReady (popMethodFrame n) := MainReady.of_view (m := popMethodFrame n) site.ready
    ((congrArg RubyCore.Frame.self hpop).trans old.self)
    ((congrArg RubyCore.Frame.defmod hpop).trans old.owner)
    ((congrArg RubyCore.Frame.cref hpop).trans old.cref)
    ((congrArg RubyCore.Frame.captured hpop).trans old.captured) scope.phase
  have hscope : ConstScopeOk (popMethodFrame n) := by
    intro x
    have he : constResolveAt (popMethodFrame n) x = mainConstResolve n.heap x := by
      simp only [constResolveAt, ready.cref, ready.owner, List.firstM, mainConstResolve]
      simp only [popMethodFrame]
      cases constOwn n.heap Boot.objectId x <;> rfl
    exact he.trans (site.constants x)
  have hden (τ : Ty) (ht : FirstOrder τ = true) (v : Value) :
      denM τ n v → denM τ (popMethodFrame n) v :=
    (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) ht rfl).mp
  refine {
    runtime := fun _ => ready
    mainSite := fun _ => site
    classRuntime := by intro cn hcn; rw [hcl] at hcn; cases hcn
    classSites := by
      intro cn hcn
      apply hn.classSites cn
      apply List.mem_append_left
      change cn ∈ κ.classes.map (·.name)
      simpa only [classSiteNames, hcl, Option.toList_none, List.append_nil] using hcn
    sat := hn.sat
    primitiveDispatch := hn.primitiveDispatch
    primitiveErrors := hn.primitiveErrors
    stringPayload := hn.stringPayload
    arrayPayload := hn.arrayPayload
    hashPayload := hn.hashPayload
    core := hn.core
    frameInRange := ⟨by rw [hp.stack]; exact hm.frameInRange.1,
      by rw [hp.stack]; exact Nat.lt_of_lt_of_le hm.frameInRange.2 hp.frames.size⟩
    env := method_pop_envOk hm.frameInRange.2 hu hc h hm.env hΓ
    selfSpine := method_pop_selfSpine hm ht.spine hm.selfLive hc h
    classes := hn.classes
    defs := hn.defs
    asms := by simp [AsmsOk, ha]
    frame := ?_
    closures := trivial
    blockTy := ?_
    selfTy := ?_
    consts := ?_
    constPaths := fun owner x τ k hx hk v hv => hden τ (ht.paths _ τ hx) v
      (hn.constPaths owner x τ k hx hk v hv)
    nested := hn.nested
    privConsts := trivial
    constScope := hscope
    exact := hn.exact
    nameFree := ?_
    bareFree := fun name hb hf _ => by rw [ready.self]; exact site.bare name hb hf
    missFree := fun hf _ owner md hl => site.missing hf owner md (by rwa [ready.self] at hl)
    query := hn.query
    clsQuery := hn.clsQuery
    declCls := hn.declCls
    baseChains := hn.baseChains
    nilQuery := hn.nilQuery
    selfLive := fun o ho => Nat.lt_of_lt_of_le (hm.selfLive o (by rwa [hpop] at ho)) hp.fields.size }
  · cases hf : κ.frame with
    | none => simpa only [FrameOk, hf, hpop] using hm.frame
    | some fr =>
      have hold : m.currentFrame.meth = fr.methName ∧
          isAName m.heap m.currentFrame.self fr.recvClass = true := by
        simpa only [FrameOk, hf] using hm.frame
      exact ⟨by rw [hpop]; exact hold.1,
        by rw [hpop]; exact hp.nominal _ _ hold.2⟩
  · cases hb : κ.blockTy with
    | none => simpa only [BlockTyOk, hb, hpop] using hm.blockTy
    | some τ =>
      obtain ⟨v, hv, hd⟩ := (show ∃ v, m.currentFrame.blk = some v ∧ denM τ m v by
        simpa only [BlockTyOk, hb] using hm.blockTy)
      exact ⟨v, by rw [hpop]; exact hv, hp.firstOrder τ (ht.block τ hb) v hd⟩
  · cases hs : κ.selfTy with
    | none => trivial
    | some τ =>
      change denM τ (popMethodFrame n) (popMethodFrame n).currentFrame.self
      rw [hpop]
      exact hp.firstOrder τ (ht.self τ hs) _ (by simpa only [SelfTyOk, hs] using hm.selfTy)
  · intro x τ hx
    obtain ⟨v, hv, hd⟩ := hn.consts x τ (by rwa [hk])
    exact ⟨v, (hscope x).trans ((hn.constScope x).symm.trans hv), hden τ (ht.consts x τ hx) v hd⟩
  · intro name hb k hmem owner md hl
    change k ∈ classOf (popMethodFrame n).heap (popMethodFrame n).currentFrame.self :: _ at hmem
    rcases List.mem_cons.mp hmem with he | he
    · subst k
      exact site.names name hb owner md (by rwa [ready.self] at hl)
    · exact hn.nameFree name hb k (List.mem_cons_of_mem _ he) owner md hl

#print axioms instance_pop_main_state
end Ratchet.Denote.Typed
