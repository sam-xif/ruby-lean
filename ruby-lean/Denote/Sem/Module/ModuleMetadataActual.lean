import Denote.Sem.Module.ModuleMethodsActual
import Denote.Sem.Class.ClassMetadataActual

/-! Constant-table-invariant metadata projections at the actual module heap. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {m : Machine} {name : String} {k : ObjId}
local notation "h₁" => heap m name

theorem metadata_old {α : Type} (hd : m.lexicalNamespace < m.heap.objs.size)
    (hk : k < m.heap.objs.size) (f : ClassPayload → α)
    (hf : ∀ cp, f { cp with consts := (name, .ref m.heap.objs.size) :: cp.consts.filter (·.1 != name) } = f cp) :
    ((h₁).classPayload? k).map f = (m.heap.classPayload? k).map f := by
  rw [(grow hd).payloadOld (by rw [hmid_size]; exact hk)]
  exact FreshClassActual.metadata_constSetIn m.heap m.lexicalNamespace k name _ f hf

theorem metadata_any_old (hd : m.lexicalNamespace < m.heap.objs.size)
    (hk : k < m.heap.objs.size) (f : ClassPayload → Bool)
    (hf : ∀ cp, f { cp with consts := (name, .ref m.heap.objs.size) :: cp.consts.filter (·.1 != name) } = f cp) :
    ((h₁).classPayload? k).any f = (m.heap.classPayload? k).any f := by
  have rule (p : Option ClassPayload) : p.any f = (p.map f).getD false := by cases p <;> rfl
  rw [rule, rule, metadata_old hd hk f hf]

theorem metadata_bind_old {α : Type} (hd : m.lexicalNamespace < m.heap.objs.size)
    (hk : k < m.heap.objs.size) (f : ClassPayload → Option α)
    (hf : ∀ cp, f { cp with consts := (name, .ref m.heap.objs.size) :: cp.consts.filter (·.1 != name) } = f cp) :
    ((h₁).classPayload? k).bind f = (m.heap.classPayload? k).bind f := by
  have rule (p : Option ClassPayload) : p.bind f = (p.map f).join := by cases p <;> rfl
  rw [rule, rule, metadata_old hd hk f hf]

theorem plain_ready_old (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    plainAllocationReadyB h₁ k = plainAllocationReadyB m.heap k :=
  metadata_any_old hd hk allocationReadyB (fun _ => rfl)

theorem module_old (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ((h₁).classPayload? k).map (·.isModule) = (m.heap.classPayload? k).map (·.isModule) :=
  metadata_old hd hk (·.isModule) (fun _ => rfl)

#print axioms metadata_old
#print axioms plain_ready_old
end Ratchet.Denote.FreshModuleActual
