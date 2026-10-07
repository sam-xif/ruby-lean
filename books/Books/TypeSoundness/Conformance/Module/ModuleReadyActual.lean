import Books.TypeSoundness.Conformance.Module.ModuleConstantsActual
import Books.TypeSoundness.Conformance.Class.ClassReady

/-! ClassReady transfers at the actual module heap. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModuleActual
open RubyCore RubyCore.Proof

theorem classReady {m : Machine} {name : String}
    (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) : ClassReady (heap m name) := by
  have ho := hc.chains.boot.2.2.2.2
  obtain ⟨eO, heO, hb⟩ := hc.objectEigen
  refine ⟨by rw [size]; exact Nat.lt_of_lt_of_le hc.bootEnd (Nat.le_add_right _ _),
    chainsIn hc.chains hd, ⟨eO, ?_, ?_⟩, ?_, ?_, constRefsLive hc.constRefs hd ho, ?_⟩
  · rw [(fields_old hd ho).2.2.1]; exact heO
  · rw [ancestors_old hc.chains hs hd (hc.chains.eigen _ ho _ heO)]; exact hb
  · rw [ancestors_old hc.chains hs hd hc.chains.boot.1]; exact hc.classBasic
  · intro e' he' base ch hbase
    rw [(fields_old hd ho).2.2.1] at he'
    exact hc.eigenSeparate e' he' base ch hbase
  · rw [ancestors_old hc.chains hs hd ho]; exact hc.objectChain

#print axioms classReady
end Checker.Soundness.FreshModuleActual
