import Books.TypeSoundness.Conformance.Module.ModuleFrameActual
import Books.TypeSoundness.Conformance.Class.ClassMethodsActual

/-! Installed-table transfers at the actual module heap. -/

set_option autoImplicit false
namespace Checker.Soundness.FreshModuleActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {m n : Machine} {name : String}  {κ : Ctx}
local notation "h₁" => heap m name

theorem own_methods (hd : m.lexicalNamespace < m.heap.objs.size) (k : ObjId) :
    (((h₁).classPayload? k).map ClassPayload.methods).getD [] =
      ((m.heap.classPayload? k).map ClassPayload.methods).getD [] := by
  by_cases hl : k < m.heap.objs.size
  · exact congrArg (fun p => p.getD []) (methods_old (name := name)  hd hl)
  · have hp := RubyCore.Proof.classPayload?_oob m.heap k hl
    by_cases hk : k = m.heap.objs.size
    · subst k; rw [hp]; simp only [Heap.classPayload?, get_module hd, namedObject, modPayload]; rfl
    · by_cases he : k = m.heap.objs.size + 1
      · subst k; rw [hp]; simp only [Heap.classPayload?, get_eigen, attachedModuleEigen]; rfl
      · rw [RubyCore.Proof.classPayload?_oob _ _ (by rw [size m name]; exact not_lt_add_two hl hk he), hp]

theorem own_code (hd : m.lexicalNamespace < m.heap.objs.size) (k : ObjId) (mn : String) :
    ((h₁).classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
      (m.heap.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) := by
  have row (g : Heap) :
      (g.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
        ((((g.classPayload? k).map ClassPayload.methods).getD []).find? (·.1 == mn)).map (·.2) := by
    cases g.classPayload? k <;> rfl
  rw [row, row, own_methods hd]

theorem classes (htop : m.lexicalNamespace = Boot.objectId) (ho : Boot.objectId < m.heap.objs.size)
    (hn : constOwn m.heap Boot.objectId name = none) (hh : n.heap = h₁) {C : CTable}
    (hp : ClassesOk C m) : ClassesOk C n := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ ho
  intro c hc
  obtain ⟨k, hk, hmethods, hsingle⟩ := hp c hc
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [hh]; exact named_old htop ho hn hk
  · intro d hd'
    obtain ⟨md, hm, hrest⟩ := hmethods d hd'
    exact ⟨md, by rw [hh, own_code hd]; exact hm, hrest⟩
  · rw [hh]
    exact hsingle.transport (Subclass.named_live hk) (fun o ho => (fields_old hd ho).2.2.1) (own_code hd)

theorem defs (hd : m.lexicalNamespace < m.heap.objs.size) (hh : n.heap = h₁) {D : DefTable}
    (hp : DefsOk D m) : DefsOk D n := by
  intro d hd'
  obtain ⟨hname, md, hm, hrest⟩ := hp d hd'
  exact ⟨hname, md, by rw [hh, own_code hd]; exact hm, hrest⟩

theorem methodsExact (hd : m.lexicalNamespace < m.heap.objs.size) (hh : n.heap = h₁)
    (hp : MethodsExact κ m) : MethodsExact κ n := by
  intro k cp hc mn md hm
  have heq := own_methods (name := name)  hd k
  rw [← hh, hc] at heq
  cases hcp : m.heap.classPayload? k with
  | none =>
    simp only [hcp, Option.map_none, Option.getD_none, Option.map_some, Option.getD_some] at heq
    rw [heq] at hm; contradiction
  | some cp₀ =>
    simp only [hcp, Option.map_some, Option.getD_some] at heq
    exact hp k cp₀ hcp mn md (heq ▸ hm)

#print axioms own_code
#print axioms classes
#print axioms defs
#print axioms methodsExact
end Checker.Soundness.FreshModuleActual
