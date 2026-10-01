import Denote.Sem.Class.ClassMethodsActual
import Denote.Sem.Class.ClassQueriesActual

/-! Repair the original hook/scope proof with main's actual empty lexical cref. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => machine m name e body

theorem hook_quiet (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hh : definitionHookQuietB m.heap Boot.objectId = true) :
    definitionHookQuietB (heap m name e) m.heap.objs.size = true := by
  unfold definitionHookQuietB
  rw [lookup_eq_methodOn, classOf_class hd, method_eigen hc hs hd (hc.eigen _ hc.boot.2.2.2.2 _ he)]
  simp only [definitionHookQuietB, lookup_eq_methodOn, classOf, he] at hh
  exact hh

theorem scope_ready (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hm : MainReady m) :
    ClassScopeReady name entry := by
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hm.cref, List.headD_nil]
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  refine ⟨m.heap.objs.size, named_fresh htop hm.classLive, ?_, ?_, ?_, ?_, hm.phase, ?_,
    hook_quiet hc hs hd he hm.hook⟩
  · change m.heap.objs.size < (heap m name e).objs.size
    rw [size]; omega
  · rw [current_frame]; rfl
  · rw [current_frame]; simp only [freshModFrame, hm.cref]
  · rw [current_frame]; rfl
  · simp only [defaultDefVis, current_frame, freshModFrame]; rfl

#print axioms hook_quiet
#print axioms scope_ready
end Ratchet.Denote.FreshClassActual
