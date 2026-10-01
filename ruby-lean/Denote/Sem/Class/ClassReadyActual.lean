import Denote.Sem.Class.ClassConstantsActual
import Denote.Sem.Class.ClassReady

/-! Retain ClassReady.subclass's original invariant transfers at the actual heap. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore RubyCore.Proof

theorem classReady {m : Machine} {name : String} {e : ObjId}
    (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size)
    (he : (m.heap.get Boot.objectId).eigen = some e) : ClassReady (heap m name e) := by
  have ho := hc.chains.boot.2.2.2.2
  have hl := hc.chains.eigen _ ho _ he
  obtain ⟨eO, heO, hb⟩ := hc.objectEigen
  refine ⟨by rw [size]; exact Nat.lt_of_lt_of_le hc.bootEnd (Nat.le_add_right _ _),
    chainsIn hc.chains hd hl, ⟨eO, ?_, ?_⟩, ?_, ?_, constRefsLive hc.constRefs hd ho, ?_⟩
  · rw [(fields_old hd ho).2.2.1]; exact heO
  · rw [ancestors_old hc.chains hs hd (hc.chains.eigen _ ho _ heO)]; exact hb
  · rw [ancestors_old hc.chains hs hd hc.chains.boot.1]; exact hc.classBasic
  · intro e' he' base ch hbase
    rw [(fields_old hd ho).2.2.1] at he'
    exact hc.eigenSeparate e' he' base ch hbase
  · rw [ancestors_old hc.chains hs hd ho]; exact hc.objectChain

#print axioms classReady
end Ratchet.Denote.FreshClassActual
