import Denote.Sem.Class.ClassAllocatorsActual

/-! Reuse the original empty-header selector and ordered-chain publication proofs. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e

theorem ordered_chain (hc : ClassReady m.heap) (hs : Saturated m.heap) (hr : RootNames m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) :
    NamedChain h₁ (name :: rootAncestors) (ancestors h₁ m.heap.objs.size) := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  rw [ordinary_chain hc hs hd]
  have roots := rootNames (e := e) (p := Boot.objectId) hr hc.constRefs htop ho hn
  exact ⟨named_fresh htop ho,
    roots.named "Object" Boot.objectId (by decide),
    roots.named "Kernel" Boot.kernelId (by decide),
    roots.named "BasicObject" Boot.basicObjectId (by decide), trivial⟩

theorem ownNames_header {C : CTable} (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassOwnNames C m.heap) :
    ClassOwnNames (classHeader name :: C) h₁ := by
  have hol := lt_size_of_classPayload ho
  apply (ownNames htop hol hn ht hp).cons_empty
  intro k hk
  have he := (named_fresh (name := name) (e := e) htop ho).symm.trans hk
  have heq := Option.some.inj he
  subst k
  simp only [ownMethods, Heap.classPayload?, get_class (htop ▸ hol), namedObject, freshClassPayload]
  rfl

theorem classChains_header {C : CTable} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hr : RootNames m.heap) (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassChains C m.heap) (hf : HeaderTableFrame C name) :
    ClassChains (classHeader name :: C) h₁ := by
  apply (classChains hc hs htop hn ht hp).publish_header hf
  intro k hk
  have he := (named_fresh (name := name) (e := e) htop ho).symm.trans hk
  have heq := Option.some.inj he
  subst k
  exact ordered_chain hc hs hr htop ho hn

#print axioms ordered_chain
#print axioms ownNames_header
#print axioms classChains_header
end Ratchet.Denote.FreshClassActual
