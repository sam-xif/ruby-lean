import Denote.Sem.InstanceSite
import Denote.Sem.ClassConstants
import Denote.Sem.ClassScopeEntry
import Denote.Sem.MetaReadyClass

/-! Fresh class creation establishes its instance dispatch/scope site. The third
NameFreeOk site is essential: instances inherit Object, not Object's metaclass. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

theorem instanceSite {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {name : String}
    {e : ObjId} {body : RubyCore.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (he : (m.heap.get Boot.objectId).eigen = some e) :
    InstanceSite κ name m.heap.objs.size (freshClsHeap m.heap Boot.objectId name name e) := by
  have ready := hm.runtime hr
  have hc := hm.core.classReady.chains
  have hs : ConstScopeOk
      (freshClsMachine m Boot.objectId m.currentFrame.cref name name e body) :=
    const_scope hc hm.sat ready.classLive ready.cref ready.owner hm.constScope
  refine ⟨classNamed_freshClass ready.classLive hc.boot.2.2.2.2, ?_,
    hook_quiet (body := body) hc hm.sat he ready.hook, ?_, ?_, meta_fresh hm.core.classReady hm.sat he⟩
  · simp only [classFrontB, Proof.Judgment.freshClsHeap_cp_k]; rfl
  · intro cn
    have hs := hs cn
    rw [constResolveAt, current_frame] at hs
    simpa only [freshModFrame, ready.cref, instanceConstResolve, freshClsMachine] using hs
  · intro n hn owner md hmd
    rw [method_class hc hm.sat] at hmd
    exact hm.nameFree n hn Boot.objectId (by simp [nameFreeSites]) owner md hmd

#print axioms instanceSite
end Ratchet.Denote.FreshClass
