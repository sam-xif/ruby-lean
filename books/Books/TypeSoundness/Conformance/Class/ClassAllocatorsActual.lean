import Books.TypeSoundness.Conformance.Class.ClassDeclaredActual

/-! Retain old allocator/name capabilities and prove readiness for the actual class. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof
variable {p : ObjId}
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e p

theorem allocators {names : List String} (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId) (hn : constOwn m.heap Boot.objectId name = none)
    (ha : AllocatorsOk names m.heap) : AllocatorsOk names h₁ := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  intro cn hcn
  obtain ⟨k, hk, hp⟩ := ha cn hcn
  exact ⟨k, named_old (p := p) htop hc.boot.2.2.2.2 hn hk,
    hp.transport (by rw [size m name e]; omega) (module_old hd hp.live)
      (ancestors_old hc hs hd hp.live) (plain_ready_old hd hp.live)⟩

theorem globalConsts {names : List String} (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size) (hc : GlobalConstsOk names m.heap) :
    GlobalConstsOk (name :: names) h₁ := by
  intro cn v hv
  by_cases hn : cn = name
  · subst cn; exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    apply hc cn v
    have he := const_other (e := e) (p := p) htop ho hn
    simp only [Subclass.const_eq_own] at he
    exact he ▸ hv

theorem ordinary_chain (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    ancestors (heap m name e) m.heap.objs.size =
      [m.heap.objs.size, Boot.objectId, Boot.kernelId, Boot.basicObjectId] := by
  rw [ancestors_class hc.chains hs hd hc.chains.boot.2.2.2.2, hc.objectChain]

theorem plain (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hf : objectClassFlagsB m.heap = true) :
    PlainAllocator (heap m name e) m.heap.objs.size := by
  have hchain := ordinary_chain (name := name) (e := e) hc hs hd
  have hne (k : ObjId) (hk : k ≤ Boot.yielderId) : m.heap.objs.size ≠ k :=
    (Nat.ne_of_lt (Nat.lt_of_le_of_lt hk hc.bootEnd)).symm
  refine ⟨?_, hne _ (by decide), hne _ (by decide), hne _ (by decide), hne _ (by decide),
    ?_, ?_, ?_, allocator_ready hd hf, ?_, ?_⟩
  · rw [size m name e]
    exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  · simp only [Heap.classPayload?, get_class hd, namedObject, freshClassPayload]; rfl
  · simp [hchain]
  · simp only [Builtins.allocatableCore, hchain]
    simp [Builtins.allocatableCore, hchain,
      Boot.objectId, Boot.kernelId, Boot.basicObjectId, Boot.stringId, Boot.arrayId,
      Boot.hashId, Boot.exceptionId]
    (repeat' apply And.intro) <;> exact hne _ (by decide)
  · simp only [hchain]
    simp [Builtins.payloadCoreClasses, hchain,
      Boot.objectId, Boot.kernelId, Boot.basicObjectId, Boot.stringId, Boot.arrayId,
      Boot.hashId, Boot.procId, Boot.integerId, Boot.floatId, Boot.symbolId, Boot.exceptionId,
      Boot.rationalId, Boot.complexId, Boot.enumeratorId, Boot.generatorId, Boot.yielderId]
    (repeat' apply And.intro) <;> exact hne _ (by decide)
  · simp only [hchain]
    simp [constructBlockers, hchain, Boot.objectId, Boot.kernelId, Boot.basicObjectId, Boot.moduleId,
      Boot.enumeratorId, Boot.generatorId, Boot.yielderId, Boot.procId, Boot.randomId,
      Boot.regexpId, Boot.rangeId, Boot.integerId, Boot.floatId, Boot.symbolId, Boot.rationalId,
      Boot.complexId, Boot.nilClassId, Boot.trueClassId, Boot.falseClassId]
    (repeat' apply And.intro) <;> exact hne _ (by decide)

#print axioms allocators
#print axioms globalConsts
#print axioms plain
end Checker.Soundness.FreshClassActual
