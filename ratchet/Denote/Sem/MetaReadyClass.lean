import Denote.Sem.MetaReady
import Denote.Sem.SubclassReady

/-! Publish metaclass readiness from fresh heap contents; preserve old sites independently
of names, methods or bodies. Object is the boot-root instance of the same contract. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

theorem ClassReady.metaObject {h : Heap} (hc : ClassReady h) : MetaReady h Boot.objectId := by
  obtain ⟨e, he, hb⟩ := hc.objectEigen
  exact ⟨e, he, hb, hc.eigenSeparate e he⟩

theorem MetaReady.subclass_old {h : Heap} {d parent eParent k : ObjId} {name q : String}
    (hm : MetaReady h k) (hc : ChainsIn h) (hs : Saturated h) (hk : k < h.objs.size) :
    MetaReady (Subclass.heap h d name q parent eParent) k :=
  hm.transport (Subclass.fields hk).2.2.1
    (fun e he => Subclass.ancestors_old hc hs (hc.eigen k hk e he))

theorem Subclass.meta_fresh {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hc : ChainsIn h) (hs : Saturated h) (hep : eParent < h.objs.size)
    (hb : (ancestors h eParent).contains Boot.basicObjectId = true) :
    MetaReady (Subclass.heap h d name q parent eParent) h.objs.size := by
  refine ⟨h.objs.size + 1, ?_, ?_, ?_⟩
  · rw [Subclass.get_class]
  · rw [Subclass.ancestors_eigen hc hs hep]
    simp only [List.contains_cons, hb, Bool.or_true]
  · intro base ch hbase
    exact (Nat.ne_of_lt (Nat.lt_succ_of_lt
      (Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.boot.2.2.2.1))).symm

theorem FreshClass.meta_fresh {h : Heap} {d : ObjId} {name q : String} {e : ObjId}
    (hc : ClassReady h) (hs : Saturated h) (he : (h.get Boot.objectId).eigen = some e) :
    MetaReady (freshClsHeap h d name q e) h.objs.size := by
  obtain ⟨e', he', hb, _⟩ := hc.metaObject
  rw [he] at he'; cases he'
  exact Subclass.meta_fresh hc.chains hs (hc.chains.eigen _ hc.chains.boot.2.2.2.2 _ he) hb

#print axioms Subclass.meta_fresh
end Ratchet.Denote
