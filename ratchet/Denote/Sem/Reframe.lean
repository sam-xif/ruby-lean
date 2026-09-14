import Denote.Sem.Transport

/-! Conformance across a frame switch at an unchanged heap. The caller/body environments
and frame predicates are supplied separately; heap conformance is reused, not re-assumed.
Behavioral types and recursive call assumptions need their own frame-change transport.
-/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure ReframeFO (κ : Ctx) (I : Ty) : Prop where
  spine : FirstOrder I = true
  self : ∀ τ, κ.selfTy = some τ → FirstOrder τ = true
  block : ∀ τ, κ.blockTy = some τ → FirstOrder τ = true
  consts : ∀ x τ, constGet? κ x = some τ → FirstOrder τ = true
  paths : ∀ x τ, envGet? κ.consts x = some τ → FirstOrder τ = true

theorem constGet?_empty {κ : Ctx} (hc : κ.consts = []) (x : String) :
    constGet? κ x = none := by
  simp [constGet?, hc, envGet?]

theorem ReframeFO.empty {κ : Ctx} {I : Ty} (hi : FirstOrder I = true)
    (hs : κ.selfTy = none) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    ReframeFO κ I := by
  refine ⟨hi, ?_, ?_, ?_, ?_⟩
  · intro τ h; rw [hs] at h; cases h
  · intro τ h; rw [hb] at h; cases h
  · intro x τ h; rw [constGet?_empty hc x] at h; cases h
  · intro x τ h; simp [hc, envGet?] at h

theorem StateOk_reframe {κ : Ctx} {Γ Γ' : Env} {I : Ty} {m n : Machine}
    {fr : Option Ratchet.Frame} (h : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (ha : κ.asms = []) (hh : n.heap = m.heap)
    (hs : n.currentFrame.self = m.currentFrame.self)
    (hb : n.currentFrame.blk = m.currentFrame.blk)
    (hc : n.currentFrame.cref = m.currentFrame.cref)
    (hd : n.currentFrame.defmod = m.currentFrame.defmod)
    (hcap : n.currentFrame.captured = m.currentFrame.captured)
    (hphase : n.preludeMode = m.preludeMode)
    (hlookup : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hr : FrameInRange n) (he : EnvOk Γ' n) (hf : FrameOk fr n) :
    StateOk (κ.withFrame fr) Γ' I n := by
  have hden (τ : Ty) (ht : FirstOrder τ = true) (v : Value) :
      denM τ m v → denM τ n v := (denM_heap_only ht hh.symm).mp
  have hresolve (x : String) : constResolveAt n x = constResolveAt m x := by
    simp only [constResolveAt, hh, hc, hd]
  have hivar : ivarOf n.heap n.currentFrame.self = ivarOf m.heap m.currentFrame.self := by
    rw [hh, hs]
  have hfree : nameFreeN (κ.withFrame fr) = nameFreeN κ := rfl
  have hcore : coreConstFreeN (κ.withFrame fr) = coreConstFreeN κ := rfl
  refine {
    runtime := fun hr => (h.runtime hr).reframe hh hs hd hc hcap hphase
    sat := by simpa only [HeapSaturated, hh] using h.sat
    primitiveDispatch := by simpa only [hh, hfree] using h.primitiveDispatch
    primitiveErrors := by simpa only [hh] using h.primitiveErrors
    stringPayload := by simpa only [hh] using h.stringPayload
    arrayPayload := by simpa only [hh] using h.arrayPayload
    hashPayload := by simpa only [hh] using h.hashPayload
    core := by simpa only [hh] using h.core
    frameInRange := hr
    env := he
    selfSpine := ?_
    classes := by simpa only [ClassesOk, hh] using h.classes
    defs := by simpa only [DefsOk, hh] using h.defs
    asms := ?_
    frame := hf
    closures := trivial
    blockTy := ?_
    selfTy := ?_
    consts := ?_
    constPaths := ?_
    nested := by simpa only [NestedClassesOk, hh] using h.nested
    privConsts := h.privConsts
    constScope := by simpa only [ConstScopeOk, hresolve, hh] using h.constScope
    exact := by simpa only [MethodsExact, hh, hfree] using h.exact
    nameFree := by simpa only [NameFreeOk, nameFreeSites, hh, hs, hfree] using h.nameFree
    bareFree := by simpa only [BareNameFree, hh, hs, hfree] using h.bareFree
    missFree := by simpa only [MissFree, hh, hs, hfree] using h.missFree
    query := by simpa only [QueryOk, hh, hfree] using h.query
    clsQuery := by simpa only [ClsQueryOk, hh, hfree] using h.clsQuery
    declCls := by simpa only [DeclClassOk, hh] using h.declCls
    baseChains := by simpa only [BaseChainsOk, hh, hcore] using h.baseChains
    nilQuery := by simpa only [NilQueryOk, hh, hfree] using h.nilQuery
    selfLive := by simpa only [SelfLive, hh, hs] using h.selfLive }
  · change denSpine I n _ ∧ _
    rw [hivar]
    refine ⟨?_, h.selfSpine.2⟩
    exact ((denM_heap_only_aux I ht.spine).2 m n _ [] hh.symm).mp h.selfSpine.1
  · change AsmsOk κ.asms n
    simp [AsmsOk, ha]
  · change BlockTyOk κ.blockTy n
    have ho := h.blockTy
    cases ht' : κ.blockTy with
    | none => simpa only [BlockTyOk, ht', hb] using ho
    | some τ =>
      obtain ⟨v, hv, hvty⟩ := (show ∃ v, m.currentFrame.blk = some v ∧ denM τ m v by
        simpa only [BlockTyOk, ht'] using ho)
      exact ⟨v, hb.trans hv, hden τ (ht.block τ ht') v hvty⟩
  · change SelfTyOk κ.selfTy n
    have ho := h.selfTy
    cases ht' : κ.selfTy with
    | none => trivial
    | some τ =>
      change denM τ n n.currentFrame.self
      rw [hs]
      exact hden τ (ht.self τ ht') _ (by simpa only [SelfTyOk, ht'] using ho)
  · intro x τ hx
    rw [hlookup] at hx
    obtain ⟨v, hv, hvty⟩ := h.consts x τ hx
    exact ⟨v, by rw [hresolve]; exact hv, hden τ (ht.consts x τ hx) v hvty⟩
  · intro owner x τ k hx hk v hv
    rw [hh] at hk hv
    exact hden τ (ht.paths _ τ hx) v (h.constPaths owner x τ k hx hk v hv)

#print axioms StateOk_reframe
end Ratchet.Denote
