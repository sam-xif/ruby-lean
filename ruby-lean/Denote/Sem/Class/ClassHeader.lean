import Denote.Sem.Class.ClassPublish
import Ratchet.Guards.ClassHeader
import Denote.Sem.Class.ClassDeclared
import Denote.Sem.Class.ClassNewEntry

/-! Publish a fresh class header without authorizing a constructor or any method body. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem FreshClass.declared_header {κ : Ctx} {m n : Machine} {name : String} {e : ObjId}
    (hc : ClassReady m.heap) (hs : Proof.Saturated m.heap) (hr : RootNames m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hq : NativeQuiet name "new")
    (hd : NewDispatch m.heap (classOf m.heap (.ref Boot.objectId)))
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m)
    (ht : HeaderTableFrame κ.classes name) : DeclClassOk (classHeaderCtx κ name) n := by
  have old := declared hc.chains hs ho hn hh hclasses hp
  intro c hmem k hk
  change c ∈ classHeader name :: κ.classes at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · change classNamed? n.heap name = some k at hk
    have hnamed := classNamed_freshClass (name := name) (e := e) ho hc.chains.boot.2.2.2.2
    rw [← hh] at hnamed
    have heq : m.heap.objs.size = k := Option.some.inj (hnamed.symm.trans hk)
    subst k
    have shape := ordinary (name := name) (d := Boot.objectId) (q := name) (e := e) hc hs
    have dispatch := new_dispatch hc.chains hs he hne hq hd
    have chain := named_chain (name := name) (e := e) hc hs hr ho hn
    rw [← hh] at shape dispatch chain
    refine ⟨shape.rooted, shape.notClass, shape.notModule, shape.module,
      fun _ => ⟨dispatch.found, dispatch.missing⟩, ?_⟩
    intro ch hch _
    change ancestors? (classHeader name :: κ.classes) name = some ch at hch
    rw [classHeader_ancestors] at hch
    cases hch
    exact chain
  · obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := old c hmem k hk
    exact ⟨hroot, hcls, hmod, hism, fun hn => hnew (ht.newMiss c hmem hn),
      fun ch hch hmix => hchain ch (ht.chain c hmem ch hch) hmix⟩

/-- Ghost publication at the existing lexical class site. All unchanged state components
retain their original meaning; only the positive table and its sites/nested claims change. -/
theorem StateOk_publish_header {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {name : String}
    (hm : StateOk κ Γ I m) (hs : κ.scope.runtimeClass = some name)
    (hn : unqualifiedClassB name = true) (hd : DeclClassOk (classHeaderCtx κ name) m)
    (ha : ∃ k, classNamed? m.heap name = some k ∧ PlainAllocator m.heap k)
    (hown : ClassOwnNames (classHeader name :: κ.classes) m.heap)
    (hchain : ClassChains (classHeader name :: κ.classes) m.heap) :
    StateOk (classHeaderCtx κ name) Γ I m := by
  exact StateOk_publish_empty_class (c := classHeader name) hm hs rfl rfl hn hd ha hown hchain

#print axioms FreshClass.declared_header
#print axioms StateOk_publish_header
end Ratchet.Denote
