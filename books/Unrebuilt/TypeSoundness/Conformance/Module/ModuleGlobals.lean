import Books.TypeSoundness.Conformance.Module.ModuleDeclared

/-! Retain old allocation capabilities and extend the executed global-name bound.
This does not grant a constructor capability for the new module. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModule
open RubyCore Checker RubyCore.Proof.Judgment

variable {h : Heap} {names : List String} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem allocators (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (hn : constOwn h Boot.objectId name = none) (ha : AllocatorsOk names h) : AllocatorsOk names h₁ := by
  intro cn hcn
  obtain ⟨k, hk, hp⟩ := ha cn hcn
  exact ⟨k, named hc.boot.2.2.2.2 hn hk,
    hp.transport (by rw [freshModHeap_size]; omega) (module_old hp.live) (ancestors_old_fresh hc hs hp.live)⟩

theorem globalConsts (ho : Boot.objectId < h.objs.size) (hc : GlobalConstsOk names h) :
    GlobalConstsOk (name :: names) h₁ := by
  intro cn v hv
  by_cases hn : cn = name
  · subst cn; exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    apply hc cn v
    have he := const_other (name := name) ho hn
    simp only [const_eq_own] at he
    exact he ▸ hv

#print axioms allocators
#print axioms globalConsts
end Checker.Soundness.FreshModule
