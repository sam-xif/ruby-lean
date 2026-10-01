import Denote.Sem.Class.ClassMethodsActual

/-! Reuse the constant-write payload split for metadata unaffected by the own table. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

/-- Registration changes constants only; any explicitly invariant projection survives. -/
theorem metadata_constSetIn {α : Type} (h : Heap) (d k : ObjId) (name : String) (v : Value)
    (f : ClassPayload → α)
    (hf : ∀ cp, f { cp with consts := (name, v) :: cp.consts.filter (·.1 != name) } = f cp) :
    ((constSetIn h d name v).classPayload? k).map f = (h.classPayload? k).map f := by
  unfold constSetIn
  cases hp : h.classPayload? d with
  | none => rfl
  | some cp =>
    by_cases hk : k = d
    · subst k
      have hl := lt_size_of_classPayload (by simp [hp] : (h.classPayload? d).isSome = true)
      simp only [Heap.setClassPayload, Heap.classPayload?, Heap.set, Heap.get,
        objs_getD_set!_self _ _ _ hl]
      change some (f { cp with consts := (name, v) :: cp.consts.filter (·.1 != name) }) =
        (h.classPayload? d).map f
      rw [hf, hp]; rfl
    · simp only [Heap.setClassPayload, Heap.classPayload?, Heap.set, Heap.get]
      rw [objs_getD_set!_ne _ _ _ _ hk]

variable {m : Machine} {name : String} {e k : ObjId}
local notation "h₁" => heap m name e

theorem metadata_old {α : Type} (hd : m.lexicalNamespace < m.heap.objs.size)
    (hk : k < m.heap.objs.size) (f : ClassPayload → α)
    (hf : ∀ cp, f { cp with consts := (name, .ref m.heap.objs.size) :: cp.consts.filter (·.1 != name) } = f cp) :
    ((h₁).classPayload? k).map f = (m.heap.classPayload? k).map f := by
  rw [(grow hd).payloadOld (by rw [hmid_size]; exact hk)]
  exact metadata_constSetIn m.heap m.lexicalNamespace k name _ f hf

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
end Ratchet.Denote.FreshClassActual
