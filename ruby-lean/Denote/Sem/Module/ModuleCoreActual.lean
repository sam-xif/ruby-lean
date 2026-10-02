import Denote.Sem.Module.ModuleDataActual
import Denote.Sem.Class.ClassCoreActual

/-! CoreOk at the actual module heap. -/

set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof

theorem core {m : Machine} {name : String} 
    (hc : CoreOk m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) : CoreOk (heap m name) := by
  have hch := hc.classReady.chains
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hch.boot.2.2.2.2
  have hl : ∀ k, k ≤ Boot.procId → k < m.heap.objs.size :=
    fun _ hk => Nat.lt_of_le_of_lt hk hch.boot.2.2.2.1
  have hr := hc.classReady.constRefs "Regexp" _ (classNamed_constOwn hc.regexpNamed)
  refine {
    classReady := classReady hc.classReady hs hd
    rootNames := rootNames hc.rootNames hc.classReady.constRefs htop ho hn
    metaConstants := by
      rw [classOf_old hd hch.boot.2.2.2.2]
      exact fallback_old hch hs htop ho (ClsGrow.classOf_lt hch hch.boot.2.2.2.2) hc.metaConstants
    basicSelf := ?_
    moduleBasic := by rw [ancestors_old hch hs hd hch.boot.2.1]; exact hc.moduleBasic
    stringNamed := named_old htop hch.boot.2.2.2.2 hn hc.stringNamed
    stringSelf := ?_
    stringBasic := ?_
    regexpNamed := named_old htop hch.boot.2.2.2.2 hn hc.regexpNamed
    regexpSelf := ?_
    regexpBasic := ?_
    procBasic := ?_
    arrayBasic := ?_
    hashBasic := ?_
    coreNamed := ?_ }
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.basicSelf
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.stringSelf
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.stringBasic
  · rw [ancestors_old hch hs hd hr]; exact hc.regexpSelf
  · rw [ancestors_old hch hs hd hr]; exact hc.regexpBasic
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.procBasic
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.arrayBasic
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.hashBasic
  · intro cn hcn v hv
    by_cases hn' : cn = name
    · subst cn
      rw [const_self htop ho] at hv
      cases hv
      exact ⟨m.heap.objs.size, rfl,
        by simp only [Heap.classPayload?, get_module hd, namedObject, Option.isSome_some]⟩
    · rw [const_other htop hch.boot.2.2.2.2 hn'] at hv
      obtain ⟨o, rfl, hp⟩ := hc.coreNamed cn hcn v hv
      exact ⟨o, rfl, (classPayload_live hd (lt_size_of_classPayload hp)).trans hp⟩

#print axioms core
end Ratchet.Denote.FreshModuleActual
