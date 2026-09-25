import Denote.Sem.Singleton.SingletonScope
import Denote.Rules.Method.MethodState

/-! Singleton scope at real required-argument entry and after a nested method returns.
Full body conformance additionally needs the distinct static frame/self contract. -/
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

#print axioms singleton_required_scope
#print axioms singleton_pop_scope
end Ratchet.Denote.Typed
