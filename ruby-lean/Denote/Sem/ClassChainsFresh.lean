import Denote.Sem.SubclassDeclared
import Denote.Sem.ClassChains
import Denote.Sem.ClassRootNames

/-! Fresh ordinary classes establish ordered name/id correspondence. Existing declared
chains survive, with explicit table framing preventing newly activated old claims. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem ordered_chain {h : Heap} {name : String} {e : ObjId}
    (hc : ClassReady h) (hs : Proof.Saturated h) (hr : RootNames h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) :
    NamedChain (freshClsHeap h Boot.objectId name name e) (name :: rootAncestors)
      (ancestors (freshClsHeap h Boot.objectId name name e) h.objs.size) := by
  rw [(ordinary hc hs).chain]
  have roots := rootNames (e := e) hr hc.constRefs ho hn
  exact ⟨classNamed_freshClass ho hc.chains.boot.2.2.2.2,
    roots.named "Object" Boot.objectId (by decide),
    roots.named "Kernel" Boot.kernelId (by decide),
    roots.named "BasicObject" Boot.basicObjectId (by decide), trivial⟩

theorem classChains {C : CTable} {m : Machine} {name : String} {e : ObjId}
    (hc : ClassReady m.heap) (hs : Proof.Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassChains C m.heap) :
    ClassChains C (freshClsHeap m.heap Boot.objectId name name e) :=
  Subclass.classChains hc hs hn ht hp

theorem classChains_header {C : CTable} {m : Machine} {name : String} {e : ObjId}
    (hc : ClassReady m.heap) (hs : Proof.Saturated m.heap) (hr : RootNames m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassChains C m.heap) (hf : HeaderTableFrame C name) :
    ClassChains (classHeader name :: C) (freshClsHeap m.heap Boot.objectId name name e) := by
  apply (classChains hc hs hn ht hp).publish_header hf
  intro k hk
  have he := (classNamed_freshClass (name := name) (e := e) ho hc.chains.boot.2.2.2.2).symm.trans hk
  have heq := Option.some.inj he
  subst k
  exact ordered_chain hc hs hr ho hn

#print axioms ordered_chain
#print axioms classChains_header
end Ratchet.Denote.FreshClass
