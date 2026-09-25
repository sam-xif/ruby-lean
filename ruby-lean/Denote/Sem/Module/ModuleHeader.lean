import Ratchet.Guards.ModuleHeader
import Denote.Sem.Module.ModuleReady
import Denote.Sem.Module.ModuleDeclared

/-! Publish a fresh module's kind and ordered ancestry while preserving earlier rows.
The table frame forbids activating previously unknown ancestry or dispatch claims. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem ordered_chain (ho : (h.classPayload? Boot.objectId).isSome = true) :
    NamedChain h₁ [name] (ancestors h₁ h.objs.size) := by
  rw [ancestors_fresh_k]
  exact ⟨named_new (lt_size_of_classPayload ho) ho, trivial⟩

theorem classChains_header {C : CTable} {m : Machine} (hc : ClassReady m.heap)
    (hs : Saturated m.heap) (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hclasses : ClassesOk C m) (hp : ClassChains C m.heap) (ht : ModuleHeaderFrame C name) :
    ClassChains (moduleHeader name :: C) (freshModHeap m.heap Boot.objectId name name) := by
  have old := classChains hc hs hn hclasses hp
  intro c hmem k hk ns hns
  rcases List.mem_cons.mp hmem with rfl | hmem
  · change ancestors? (moduleHeader name :: C) name = some ns at hns
    rw [moduleHeader_ancestors] at hns
    cases hns
    have he := Option.some.inj ((named_new (name := name) (lt_size_of_classPayload ho) ho).symm.trans hk)
    subst k
    exact ordered_chain ho
  · exact old c hmem k hk ns (ht.chain c hmem ns hns)

theorem declared_header {κ : Ctx} {m : Machine} (hc : ClassReady m.heap)
    (hs : Saturated m.heap) (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m)
    (ht : ModuleHeaderFrame κ.classes name) :
    DeclClassOk (moduleHeaderCtx κ name)
      { m with heap := freshModHeap m.heap Boot.objectId name name } := by
  have old := declared (n := { m with heap := freshModHeap m.heap Boot.objectId name name })
    hc.chains hs ho hn rfl hclasses hp
  intro c hmem k hk
  change c ∈ moduleHeader name :: κ.classes at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · have he := Option.some.inj ((named_new (name := name) hc.chains.boot.2.2.2.2 ho).symm.trans hk)
    subst k
    refine ⟨by simp [moduleHeader], (Nat.ne_of_lt hc.chains.boot.1).symm,
      (Nat.ne_of_lt hc.chains.boot.2.1).symm, ?_, by simp [moduleHeader], ?_⟩
    · simp only [freshModHeap_cp_k, Option.map_some, moduleHeader]
    · intro ns hns _
      change ancestors? (moduleHeader name :: κ.classes) name = some ns at hns
      rw [moduleHeader_ancestors] at hns
      cases hns
      change (∀ cn ∈ [name], ∃ j, classNamed? _ cn = some j ∧ (ancestors _ _).contains j = true) ∧
        (∀ cn j, classNamed? _ cn = some j → (ancestors _ _).contains j = true → cn ∈ [name])
      rw [ancestors_fresh_k]
      constructor
      · intro cn hcn
        have he := List.mem_singleton.mp hcn
        subst cn
        exact ⟨m.heap.objs.size, named_new hc.chains.boot.2.2.2.2 ho, by simp⟩
      · intro cn j hcn hj
        have he : j = m.heap.objs.size := by simpa using hj
        subst j
        exact List.mem_singleton.mpr (fresh_name_only hc.constRefs hc.chains.boot.2.2.2.2 hcn)
  · obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := old c hmem k hk
    exact ⟨hroot, hcls, hmod, hism, fun hk hn => hnew hk (ht.newMiss c hmem hn),
      fun ch hch hmix => hchain ch (ht.chain c hmem ch hch) hmix⟩

#print axioms classChains_header
#print axioms declared_header
end Ratchet.Denote.FreshModule
