import Denote.Sem.Closure.DeadFrame
import Denote.Sem.Core.Framed

/-! Full conformance survives a dead frame-store push: the stack, the current frame, the heap
and every live capture chain are unchanged, and lookup fuel only grows. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem currentFrame_pushDead {m : Machine} (hr : FrameInRange m) (f : RubyCore.Frame) :
    (pushDead m f).currentFrame = m.currentFrame := by
  rw [currentFrame_headD (m := pushDead m f) hr.1, currentFrame_headD hr.1]
  exact pushDead_getD hr.2

theorem getLocal_pushDead {m : Machine} (hl : CaptureLive m (some (m.stack.headD 0)))
    (f : RubyCore.Frame) (x : String) : (pushDead m f).getLocal x = m.getLocal x := by
  simp only [Machine.getLocal]
  have hs : (pushDead m f).frames.size = m.frames.size + 1 := by simp [pushDead]
  change Machine.getLocal.go (pushDead m f) x (m.stack.headD 0) ((pushDead m f).frames.size + 1) = _
  rw [hs]
  rw [getLocal_go_eq_frameLocal_go _ x _ _ (hl.pushDead f),
    getLocal_go_eq_frameLocal_go _ x _ _ hl,
    frameLocal_go_preserved (n := pushDead m f) (fun _ hi => pushDead_getD hi) x _ _ hl,
    frameLocal_go_fuel hl x _ (by omega),
    frameLocal_go_fuel hl x (m.frames.size + 1) (by omega)]

theorem constResolveAt_pushDead {m : Machine} (hr : FrameInRange m) (f : RubyCore.Frame)
    (n : String) : constResolveAt (pushDead m f) n = constResolveAt m n := by
  unfold constResolveAt Interp.lexicalConstant Machine.lexicalNamespace
  rw [currentFrame_pushDead hr f]
  rfl

theorem StateOk_pushDead {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (h : StateOk κ Γ I m) (f : RubyCore.Frame) : StateOk κ Γ I (pushDead m f) := by
  have hr := h.frameInRange
  have hcf := currentFrame_pushDead hr f
  have hl : CaptureLive m (some (m.stack.headD 0)) := h.toStateCore.captureLive
  have hgl := getLocal_pushDead hl f
  have h0 : 0 < m.frames.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hr.2
  have hph : (pushDead m f).heap = m.heap := rfl
  have hden : ∀ τ v, denM τ m v → denM τ (pushDead m f) v := fun _ _ hv => denM_pushDead f h0 hv
  exact {
    runtime := fun hr' => (h.runtime hr').reframe rfl (by rw [hcf]) (by rw [hcf]) (by rw [hcf])
      (by rw [hcf]) rfl (by rw [hcf]) (by rw [hcf])
    mainSite := h.mainSite
    moduleBase := h.moduleBase
    classRuntime := by
      intro cn hr'
      obtain ⟨k, hk⟩ := h.classRuntime cn hr'
      exact ⟨k, hk.reframe rfl (by rw [hcf]) (by rw [hcf]) (by rw [hcf]) rfl
        (by simp only [defaultDefVis, hcf]) (by rw [hcf]) (by rw [hcf]) (by rw [hcf]) (by rw [hcf])⟩
    singletonRuntime := by
      intro cn hr'
      obtain ⟨k, e, scope⟩ := h.singletonRuntime cn hr'
      exact ⟨k, e, scope.reframe rfl (by rw [hcf]) (by rw [hcf]) (by rw [hcf]) (by rw [hcf]) rfl⟩
    classSites := h.classSites
    allocators := h.allocators
    globalConsts := h.globalConsts
    sat := h.sat
    primitiveDispatch := h.primitiveDispatch
    primitiveErrors := h.primitiveErrors
    primitiveInit := h.primitiveInit
    stringPayload := h.stringPayload
    arrayPayload := h.arrayPayload
    hashPayload := h.hashPayload
    frozenFields := h.frozenFields
    core := h.core
    frameInRange := ⟨hr.1, Nat.lt_of_lt_of_le hr.2 (by simp [pushDead])⟩
    env := ⟨fun x τ hx => by
        rw [hgl]
        exact ⟨hden _ _ (h.env.1 x τ hx).1, fun y ρ hy => by rw [hgl]; exact (h.env.1 x τ hx).2 y ρ hy⟩,
      fun x hx => by rw [hgl]; exact h.env.2 x hx⟩
    selfSpine := ⟨by rw [hcf]; exact denSpine_pushDead f h0 h.selfSpine.1,
      fun x hx hc => by rw [hcf]; exact h.selfSpine.2 x hx hc⟩
    classes := by first | exact h.classes | (simpa only [hcf, hgl] using h.classes)
    defs := by first | exact h.defs | (simpa only [hcf, hgl] using h.defs)
    asms := fun a ha m₂ hl => h.asms a ha m₂ ((later_pushDead m f).trans hl)
    frame := by
      have hf := h.frame
      rcases hk : κ.frame with _ | fr <;> simp only [FrameOk, hk] at hf ⊢ <;> rw [hcf]
      · exact hf
      · exact ⟨hf.1, hden _ _ hf.2.1, hf.2.2⟩
    closures := trivial
    blockTy := by
      have hb := h.blockTy
      rcases hk : κ.blockTy with _ | β <;> simp only [BlockTyOk, hk] at hb ⊢ <;> rw [hcf]
      · exact hb
      · obtain ⟨b, h1, h2⟩ := hb; exact ⟨b, h1, hden _ _ h2⟩
    selfTy := by
      have hs := h.selfTy
      rcases hk : κ.selfTy with _ | σ <;> simp only [SelfTyOk, hk] at hs ⊢
      rw [hcf]; exact hden _ _ hs
    consts := by
      intro n τ hn
      obtain ⟨v, hv, hd⟩ := h.consts n τ hn
      exact ⟨v, by rw [constResolveAt_pushDead hr f]; exact hv, hden _ _ hd⟩
    constPaths := fun owner n τ k hn hk v hv => hden _ _ (h.constPaths owner n τ k hn hk v hv)
    nested := by first | exact h.nested | (simpa only [hcf, hgl] using h.nested)
    privConsts := by first | exact h.privConsts | (simpa only [hcf, hgl] using h.privConsts)
    constScope := by
      intro n
      rw [constResolveAt_pushDead hr f]; exact h.constScope n
    exact := by first | exact h.exact | (simpa only [hcf, hgl] using h.exact)
    nameFree := by
      intro n hn k hk
      exact h.nameFree n hn k (by simpa only [nameFreeSites, hcf, hph] using hk)
    bareFree := by
      intro n hb hf hs
      rw [hcf]; exact h.bareFree n hb hf hs
    missFree := by
      intro hf hs
      rw [hcf]; exact h.missFree hf hs
    query := by first | exact h.query | (simpa only [hcf, hgl] using h.query)
    clsQuery := by first | exact h.clsQuery | (simpa only [hcf, hgl] using h.clsQuery)
    declCls := by first | exact h.declCls | (simpa only [hcf, hgl] using h.declCls)
    baseChains := by first | exact h.baseChains | (simpa only [hcf, hgl] using h.baseChains)
    nilQuery := by first | exact h.nilQuery | (simpa only [hcf, hgl] using h.nilQuery)
    selfLive := by
      intro o ho
      rw [hcf] at ho; exact h.selfLive o ho
    names := h.names
    localAlias := by rw [hcf]; exact h.localAlias
    capturedLive := by rw [hcf]; exact h.capturedLive.pushDead f
    rootClean := h.rootClean
    ownNames := h.ownNames
    classChains := h.classChains
    rootInit := h.rootInit }

theorem Framed_pushDead {m : Machine} (hr : FrameInRange m) (f : RubyCore.Frame) :
    Framed m (pushDead m f) := by
  have h0 : 0 < m.frames.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hr.2
  have hg : ∀ i, i < m.frames.size → (pushDead m f).frames.getD i default = m.frames.getD i default :=
    fun _ hi => pushDead_getD hi
  refine ⟨rfl, fun _ h => h, fun _ _ h => h, fun τ _ v hv => denM_pushDead f h0 hv,
    ⟨by simp [pushDead], congrArg frameScope (hg _ hr.2), fun _ i hi _ => hg i hi,
      fun i hi _ => by rw [hg i hi], fun _ i hi _ => hg i hi, .of_frames hg, .of_frames rfl hg,
      .of_frames (fun i hi _ => hg i hi)⟩,
    ⟨Nat.le_refl _, fun _ _ _ _ _ h => denM_pushDead f h0 h⟩, fun _ _ _ h => h, .refl _, rfl, id⟩

end Ratchet.Denote
#print axioms Ratchet.Denote.StateOk_pushDead
