import Ratchet.Guards.SubclassHeader
import Denote.Sem.Class.ClassPublish
import Denote.Sem.Subclass.SubclassAllocator
import Denote.Sem.Subclass.SubclassNamedChain
import Denote.Sem.Subclass.SubclassNewEntry

/-! Publish the executed subclass's actual ancestry and allocator. Positive initializer
code and body safety are not inferred, even when all own method tables are empty. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet

variable {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
variable {c : Cls} {name : String} {parent eParent : ObjId}

theorem declared_header (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (ha : PlainAllocator m.heap parent) (he : (m.heap.get parent).eigen = some eParent)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hq : FreshClass.NativeQuiet name "new") (hnew : smroGet? κ.classes c.name "new" = none)
    (ht : SubclassHeaderFrame κ.classes name c.name)
    (hh : n.heap = heap m.heap Boot.objectId name name parent eParent) :
    DeclClassOk (subclassHeaderCtx κ name c.name) n := by
  have ready := hm.core.classReady
  have ho := (hm.runtime hr).classLive
  have old := declared ready.chains hm.sat ho hn hh hm.classes hm.declCls
  have parentDecl := hm.declCls c hc parent hp
  have newDispatch : NewDispatch m.heap (classOf m.heap (.ref parent)) := ⟨
    (parentDecl.2.2.2.2.1 hnew).1, (parentDecl.2.2.2.2.1 hnew).2⟩
  obtain ⟨ns, hparent, hchild⟩ := ht.chain
  intro record hrecord k hk
  change record ∈ subclassHeader name c.name :: κ.classes at hrecord
  rcases List.mem_cons.mp hrecord with rfl | hrecord
  · change classNamed? n.heap name = some k at hk
    have hn' := named_fresh (name := name) (q := name) (parent := parent) (eParent := eParent) ho
    rw [← hh] at hn'
    have heq := Option.some.inj (hn'.symm.trans hk)
    subst k
    have shape := plain (d := Boot.objectId) (name := name) (q := name) (eParent := eParent) hm.core hm.sat ha
    have dispatch := new_dispatch (d := Boot.objectId) (name := name) ready.chains hm.sat ha.live he hne hq newDispatch
    rw [← hh] at shape dispatch
    refine ⟨shape.rooted, shape.notClass, shape.notModule, shape.module,
      fun _ => ⟨dispatch.found, dispatch.missing⟩, ?_⟩
    intro ch hch hmix
    change ancestors? (subclassHeader name c.name :: κ.classes) name = some ch at hch
    rw [hchild] at hch
    cases hch
    obtain ⟨hpos, hneg⟩ := parentDecl.2.2.2.2.2 ns hparent hmix
    simpa only [hh, List.cons_append] using named_chain (name := name) (q := name) (eParent := eParent)
      ready hm.sat ho hn ha.live hpos hneg
  · obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := old record hrecord k hk
    exact ⟨hroot, hcls, hmod, hism, fun hn => hnew (ht.old.newMiss record hrecord hn),
      fun ch hch hmix => hchain ch (ht.old.chain record hrecord ch hch) hmix⟩

theorem ownNames_header (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) :
    ClassOwnNames (subclassHeader name c.name :: κ.classes)
      (heap m.heap Boot.objectId name name parent eParent) := by
  apply (ownNames hm.core.classReady.chains.boot.2.2.2.2 hn hm.classes hm.ownNames).cons_empty
  intro k hk
  have he := (named_fresh (name := name) (q := name) (parent := parent) (eParent := eParent)
    (hm.runtime hr).classLive).symm.trans hk
  have heq := Option.some.inj he
  subst k
  simp only [ownMethods, Heap.classPayload?, get_class, classObjE, Option.map_some, Option.getD_some]

theorem classChains_header (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : SubclassHeaderFrame κ.classes name c.name) :
    ClassChains (subclassHeader name c.name :: κ.classes)
      (heap m.heap Boot.objectId name name parent eParent) := by
  have ready := hm.core.classReady
  have old := classChains (q := name) (parent := parent) (eParent := eParent)
    ready hm.sat hn hm.classes hm.classChains
  obtain ⟨ns, hparent, hchild⟩ := ht.chain
  intro record hrecord k hk ch hch
  rcases List.mem_cons.mp hrecord with rfl | hrecord
  · change classNamed? _ name = some k at hk
    have he := (named_fresh (name := name) (q := name) (parent := parent) (eParent := eParent)
      (hm.runtime hr).classLive).symm.trans hk
    have heq := Option.some.inj he
    subst k
    change ancestors? (subclassHeader name c.name :: κ.classes) name = some ch at hch
    rw [hchild] at hch
    cases hch
    exact ordered_chain ready.chains hm.sat (hm.runtime hr).classLive hn (named_live hp)
      (hm.classChains c hc parent hp ns hparent)
  · exact old record hrecord k hk ch (ht.old.chain record hrecord ch hch)

theorem publish_header (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hs : StateOk (classBodyCtx κ name) [] .ivar0 n)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (halloc : c.name ∈ κ.pos.plainAlloc) (he : (m.heap.get parent).eigen = some eParent)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hq : FreshClass.NativeQuiet name "new") (hnew : smroGet? κ.classes c.name "new" = none)
    (ht : SubclassHeaderFrame κ.classes name c.name) (hplain : unqualifiedClassB name = true)
    (hh : n.heap = heap m.heap Boot.objectId name name parent eParent) :
    StateOk (subclassHeaderCtx (classBodyCtx κ name) name c.name) [] .ivar0 n := by
  obtain ⟨k, hk, ha⟩ := hm.allocators c.name halloc
  have heq := Option.some.inj (hp.symm.trans hk)
  subst k
  apply StateOk_publish_empty_class (c := subclassHeader name c.name) hs rfl rfl rfl hplain
  · exact declared_header (κ := κ) hm hr hc hp ha he hn hne hq hnew ht hh
  · refine ⟨m.heap.objs.size, ?_, ?_⟩
    · rw [hh]; exact named_fresh (hm.runtime hr).classLive
    · rw [hh]; exact plain hm.core hm.sat ha
  · rw [hh]; exact ownNames_header (κ := κ) hm hr hn
  · rw [hh]; exact classChains_header (κ := κ) hm hr hc hp hn ht

#print axioms declared_header
#print axioms ownNames_header
#print axioms classChains_header
#print axioms publish_header
end Ratchet.Denote.Subclass
