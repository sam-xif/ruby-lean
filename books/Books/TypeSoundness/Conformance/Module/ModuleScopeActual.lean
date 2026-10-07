import Books.TypeSoundness.Conformance.Module.ModuleMethodsActual
import Books.TypeSoundness.Conformance.Module.ModuleQueriesActual
import Books.TypeSoundness.Conformance.Module.ModuleBase
import Books.TypeSoundness.Conformance.Class.ClassScopeActual

/-! Hook/scope readiness of the actual module body with main's empty lexical cref. -/

set_option autoImplicit false
namespace Checker.Soundness.FreshModuleActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String}  {body : RubyCore.Expr}
local notation "entry" => machine m name body

theorem hook_quiet (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hh : moduleHookQuietB m.heap = true) :
    definitionHookQuietB (heap m name) m.heap.objs.size = true := by
  unfold definitionHookQuietB
  rw [lookup_eq_methodOn, classOf_module hd, method_eigen hc hs hd]
  exact hh

theorem scope_ready (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hb : moduleHookQuietB m.heap = true) (hm : MainReady m) :
    ClassScopeReady name entry := by
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hm.cref, List.headD_nil]
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  refine ⟨m.heap.objs.size, named_fresh htop hm.classLive, ?_, ?_, ?_, ?_, hm.phase, ?_,
    hook_quiet hc hs hd hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change m.heap.objs.size < (heap m name).objs.size
    rw [size]; omega
  · rw [current_frame]; rfl
  · rw [current_frame]; simp only [freshModFrame, hm.cref]
  · rw [current_frame]; rfl
  · simp only [defaultDefVis, current_frame, freshModFrame]; rfl
  · rw [current_frame]; rfl
  · rw [current_frame]; rfl
  · change ((heap m name).classPayload? m.heap.objs.size).bind (·.attached) = none
    simp only [Heap.classPayload?, get_module hd, namedObject, modPayload]; rfl
  · change ((heap m name).get m.heap.objs.size).frozen = false
    rw [get_module hd]; rfl
  · change Boot.mainId < (heap m name).objs.size
    rw [size]; exact Nat.lt_of_lt_of_le hm.live (Nat.le_add_right _ _)
  · change m.heap.objs.size ≠ classOf (heap m name) (.ref Boot.mainId)
    rw [classOf_old hd hm.live]
    exact (Nat.ne_of_lt (ClsGrow.classOf_lt hc hm.live)).symm
  · rw [current_frame]; rfl
  · rw [current_frame]; rfl

#print axioms hook_quiet
#print axioms scope_ready
end Checker.Soundness.FreshModuleActual
