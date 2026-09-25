import Denote.Sem.Core.Ready

/-! Physical scope of a singleton activation. Its class-valued self and lexical cref
refer to the named class; defmod refers to that class's cached eigenclass. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure SingletonScopeAt (cn : String) (k e : ObjId) (m : Machine) : Prop where
  named : classNamed? m.heap cn = some k
  live : k < m.heap.objs.size
  cached : (m.heap.get k).eigen = some e
  self : m.currentFrame.self = .ref k
  owner : m.currentFrame.defmod = e
  cref : m.currentFrame.cref = [k, Boot.objectId]
  captured : m.currentFrame.captured = none
  phase : m.preludeMode = false

def SingletonScopeReady (cn : String) (m : Machine) : Prop := ∃ k e, SingletonScopeAt cn k e m
def SingletonRuntimeOk (κ : Ratchet.Ctx) (m : Machine) : Prop :=
  ∀ cn, κ.scope.runtimeSingleton = some cn → SingletonScopeReady cn m

theorem SingletonScopeAt.reframe {cn : String} {k e : ObjId} {m n : Machine}
    (h : SingletonScopeAt cn k e m) (hh : n.heap = m.heap)
    (hs : n.currentFrame.self = m.currentFrame.self)
    (ho : n.currentFrame.defmod = m.currentFrame.defmod)
    (hc : n.currentFrame.cref = m.currentFrame.cref)
    (hcap : n.currentFrame.captured = m.currentFrame.captured)
    (hp : n.preludeMode = m.preludeMode) : SingletonScopeAt cn k e n :=
  ⟨by simpa only [hh] using h.named, by simpa only [hh] using h.live,
    by simpa only [hh] using h.cached, hs.trans h.self, ho.trans h.owner,
    hc.trans h.cref, hcap.trans h.captured, hp.trans h.phase⟩

theorem SingletonScopeReady.setLocal {cn : String} {m : Machine}
    (h : SingletonScopeReady cn m) (x : String) (v : Value) :
    SingletonScopeReady cn (m.setLocal x v) := by
  obtain ⟨k, e, h⟩ := h
  exact ⟨k, e, h.reframe (setLocal_heap ..) (currentFrame_setLocal_self ..)
    (currentFrame_setLocal_defmod ..) (currentFrame_setLocal_cref ..)
    (currentFrame_setLocal_captured ..) rfl⟩

theorem SingletonScopeReady.ext {cn : String} {m n : Machine}
    (h : SingletonScopeReady cn m) (he : Ext m n) (hp : n.preludeMode = m.preludeMode) :
    SingletonScopeReady cn n := by
  obtain ⟨k, e, h⟩ := h
  exact ⟨k, e, ⟨by simpa only [he.classNamed?_eq] using h.named,
    Nat.lt_of_lt_of_le h.live he.size, by rw [he.get k h.live]; exact h.cached,
    by simpa only [he.currentFrame_eq] using h.self,
    by simpa only [he.currentFrame_eq] using h.owner,
    by simpa only [he.currentFrame_eq] using h.cref,
    by simpa only [he.currentFrame_eq] using h.captured, hp.trans h.phase⟩⟩

end Ratchet.Denote
