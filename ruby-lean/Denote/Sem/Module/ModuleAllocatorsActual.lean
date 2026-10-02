import Denote.Sem.Module.ModuleDeclaredActual
import Denote.Sem.Class.ClassAllocatorsActual

/-! Old allocator/global-constant capabilities at the actual module heap. -/


set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof
variable {m : Machine} {name : String} 
local notation "h₁" => heap m name

theorem allocators {names : List String} (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId) (hn : constOwn m.heap Boot.objectId name = none)
    (ha : AllocatorsOk names m.heap) : AllocatorsOk names h₁ := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  intro cn hcn
  obtain ⟨k, hk, hp⟩ := ha cn hcn
  exact ⟨k, named_old htop hc.boot.2.2.2.2 hn hk,
    hp.transport (by rw [size m name]; omega) (module_old hd hp.live)
      (ancestors_old hc hs hd hp.live) (plain_ready_old hd hp.live)⟩

theorem globalConsts {names : List String} (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size) (hc : GlobalConstsOk names m.heap) :
    GlobalConstsOk (name :: names) h₁ := by
  intro cn v hv
  by_cases hn : cn = name
  · subst cn; exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    apply hc cn v
    have he := const_other  htop ho hn
    simp only [Subclass.const_eq_own] at he
    exact he ▸ hv

#print axioms allocators
end Ratchet.Denote.FreshModuleActual
