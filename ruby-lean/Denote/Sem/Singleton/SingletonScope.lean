import Denote.Sem.Core.State
import Denote.Sem.Core.FramedNames
import Denote.Sem.Singleton.SingletonActivation

/-! Singleton activations retain lexical class cref but use its metaclass as defmod.
Constant lookup still uses the lexical namespace, rather than the definee. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem InstanceSite.singleton_constScope {κ : Ctx} {cn : String} {k : ObjId} {m : Machine}
    (site : InstanceSite κ cn k m.heap)
    (hcref : m.currentFrame.cref = [k])
    (_howner : m.currentFrame.defmod = classOf m.heap (.ref k)) : ConstScopeOk m := by
  intro name
  simpa only [constResolveAt, Interp.lexicalConstant, Machine.lexicalNamespace,
    hcref, List.headD_cons, instanceConstResolve] using site.constants name

theorem SingletonScopeAt.constScope {κ : Ctx} {cn : String} {k e : ObjId} {m : Machine}
    (scope : SingletonScopeAt cn k e m) (site : InstanceSite κ cn k m.heap) :
    ConstScopeOk m :=
  site.singleton_constScope scope.cref (by simp only [scope.owner, classOf, scope.cached])

/-- A nested call may grow the heap, but it cannot redirect the saved singleton owner.
The phase premise comes from the callee's runtime conformance. -/
theorem SingletonScopeAt.framed {cn : String} {k e : ObjId} {m n : Machine}
    (scope : SingletonScopeAt cn k e m) (h : Framed m n) (hl : m.stack ≠ [])
    (hp : n.preludeMode = false) : SingletonScopeAt cn k e n := by
  have hs : frameScope n.currentFrame = frameScope m.currentFrame := by
    rw [currentFrame_headD (by rw [h.stack]; exact hl), currentFrame_headD hl]
    exact h.frames.scope
  exact ⟨h.classNamed scope.named, Nat.lt_of_lt_of_le scope.live h.fields.size,
    h.cachedEigen k scope.live e scope.cached,
    (congrArg FrameScope.self hs).trans scope.self,
    (congrArg FrameScope.defmod hs).trans scope.owner,
    (congrArg FrameScope.cref hs).trans scope.cref,
    (congrArg FrameScope.captured hs).trans scope.captured, hp⟩

#print axioms InstanceSite.singleton_constScope
#print axioms SingletonScopeAt.framed
end Ratchet.Denote
