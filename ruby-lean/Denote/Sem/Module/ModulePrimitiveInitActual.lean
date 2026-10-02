import Denote.Sem.Module.ModuleMethodsActual
import Denote.Sem.Module.ModuleDispatchActual
import Denote.Sem.Class.ClassPrimitiveInitActual

/-! primitiveInitB at the actual module heap. -/

set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof
variable {m : Machine} {name : String} 
local notation "h₁" => heap m name

theorem primitiveInit (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hnames : NamesOk m.heap) (hd : m.lexicalNamespace < m.heap.objs.size) :
    primitiveInitB h₁ = primitiveInitB m.heap := by
  have hz : Boot.zeroDivisionErrorId < m.heap.objs.size :=
    Nat.lt_of_le_of_lt (by decide : Boot.zeroDivisionErrorId ≤ Boot.yielderId) hc.bootEnd
  have hown (k : ObjId) : errorInitOwn h₁ k = errorInitOwn m.heap k := own_code hd k "initialize"
  have hshape : primitiveInitShapeB h₁ = primitiveInitShapeB m.heap := by
    unfold primitiveInitShapeB
    rw [ancestors_old hc.chains hs hd hz, hown, hown, hown]
  simp only [primitiveInitB, hshape, primitiveInitClasses, List.all_cons, List.all_nil, Bool.and_true]
  rw [method_old hc.chains hs hd hz]
  cases hv : Interp.methodOn m.heap Boot.zeroDivisionErrorId "initialize" with
  | none => rfl
  | some pair =>
    rcases pair with ⟨owner, md⟩
    simp only
    rw [shadow_before_old (name := name)  hnames hc.chains hs hd hz owner "initialize"]

#print axioms primitiveInit
end Ratchet.Denote.FreshModuleActual
