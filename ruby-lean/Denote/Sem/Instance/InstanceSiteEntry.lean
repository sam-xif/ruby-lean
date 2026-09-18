import Denote.Sem.Subclass.SubclassSites
import Denote.Sem.Instance.InstanceSite
import Denote.Sem.Class.ClassConstants
import Denote.Sem.Class.ClassScopeEntry
import Denote.Sem.Subclass.MetaReadyClass

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
  obtain ⟨ep, hep, hb⟩ := hm.core.classReady.objectEigen
  rw [he] at hep; cases hep
  apply Subclass.instanceSite hc hm.sat ready.classLive hc.boot.2.2.2.2 he hb ready.hook
    (Subclass.fallback_of_main ready.cref ready.owner hm.constScope)
  · intro n hn owner md hmd
    exact hm.nameFree n hn Boot.objectId (by simp [nameFreeSites]) owner md hmd
  · intro n hn owner md hmd
    have hco : classOf m.heap (.ref Boot.objectId) = e := by simp only [classOf, he]
    exact hm.nameFree n hn e (by simp [nameFreeSites, hco]) owner md hmd

#print axioms instanceSite
end Ratchet.Denote.FreshClass
