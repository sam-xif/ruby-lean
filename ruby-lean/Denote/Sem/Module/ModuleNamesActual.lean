import Denote.Sem.Module.ModuleHeapActual
import Denote.Sem.Class.ClassNamesActual

/-! Named growth for the actual module and its attached metaclass. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

namespace FreshModuleActual

theorem classPath_go_module {m : Machine} {name : String} 
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) (fuel : Nat) :
    classPath.go (heap m name) (fuel + 1) m.heap.objs.size = name := by
  simp [classPath.go, Heap.classPayload?, get_module hd, namedObject, modPayload, hn]

theorem className_go_module {m : Machine} {name : String} 
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) (fuel : Nat) :
    className.go (heap m name) (fuel + 1) m.heap.objs.size = name := by
  simp [className.go, Heap.classPayload?, get_module hd, namedObject, modPayload, modPayload,
    classPath, classPath_go_module hd hn]

theorem className_go_eigen {m : Machine} {name : String} 
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) (fuel : Nat) :
    className.go (heap m name) (fuel + 2) (m.heap.objs.size + 1) =
      "#<Class:" ++ name ++ ">" := by
  rw [className.go]
  simp [Heap.classPayload?, get_eigen, attachedModuleEigen,
    get_module hd, namedObject, modPayload, className_go_module hd hn]
  rfl

theorem namesOk {m : Machine} {name : String} 
    (hc : ChainsIn m.heap) (hn : NamesOk m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hne : name.isEmpty = false) :
    NamesOk (heap m name) := by
  have hm := namesOk_constSetIn hn m.lexicalNamespace name (.ref m.heap.objs.size)
  apply namesOk_freshGrow (grow hd) hm
  · intro k hk cp hp
    rw [hmid_size] at hk
    have hl : k < (heap m name).objs.size := by
      by_cases hbound : k < (heap m name).objs.size
      · exact hbound
      · rw [classPayload?_oob _ _ hbound] at hp
        cases hp
    rcases fresh_cases hk hl with rfl | rfl
    · simp only [Heap.classPayload?, get_module hd, namedObject] at hp
      cases hp
      refine ⟨?_, fun o ha => by cases ha⟩
      simp [classOf, get_module hd, size]
    · simp only [Heap.classPayload?, get_eigen, attachedModuleEigen] at hp
      cases hp
      refine ⟨?_, ?_⟩
      · simp only [classOf, get_eigen, attachedModuleEigen, size]
        exact Nat.lt_of_lt_of_le hc.boot.1 (Nat.le_add_right _ _)
      · intro o ha
        have heq : o = m.heap.objs.size := (Option.some.inj ha).symm
        subst o
        constructor
        · rw [size m name]; exact Nat.lt_add_of_pos_right (by decide)
        · rw [get_module hd]
          exact Nat.lt_of_lt_of_le hc.boot.2.1 (by rw [size]; omega)
  · intro k hk
    rw [hmid_size] at hk
    by_cases hl : k < (heap m name).objs.size
    · rcases fresh_cases hk hl with rfl | rfl
      · simp only [size, classPath_go_module hd hne]
      · simp [size, classPath.go, Heap.classPayload?, get_eigen, attachedModuleEigen]
    · have hz : 0 < (heap m name).objs.size := by rw [size]; omega
      obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hz)
      simp [hs, classPath.go, classPayload?_oob _ _ hl]
  · intro k hk
    rw [hmid_size] at hk
    by_cases hl : k < (heap m name).objs.size
    · rcases fresh_cases hk hl with rfl | rfl
      · simp only [size, className_go_module hd hne]
      · simp only [size, className_go_eigen hd hne]
    · have hz : 0 < (heap m name).objs.size := by rw [size]; omega
      obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hz)
      simp [hs, className.go, classPayload?_oob _ _ hl]

theorem className_old {m : Machine} {name : String} {k : ObjId}
    (hn : NamesOk m.heap) (hd : m.lexicalNamespace < m.heap.objs.size)
    (hk : k < m.heap.objs.size) : className (heap m name) k = className m.heap k := by
  have hg := grow (name := name)  hd
  rw [Proof.className_old hg.size hg.get
    (namesOk_constSetIn hn m.lexicalNamespace name (.ref m.heap.objs.size))
    (by rw [hmid_size]; exact hk)]
  exact className_constSetIn m.heap m.lexicalNamespace k name _

theorem classPath_module {m : Machine} {name : String} 
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) :
    classPath (heap m name) m.heap.objs.size = name :=
  classPath_go_module hd hn _

theorem className_module {m : Machine} {name : String} 
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) :
    className (heap m name) m.heap.objs.size = name :=
  className_go_module hd hn _

theorem className_eigen {m : Machine} {name : String} 
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) :
    className (heap m name) (m.heap.objs.size + 1) = "#<Class:" ++ name ++ ">" := by
  simpa only [className, size] using className_go_eigen hd hn (m.heap.objs.size + 1)

#print axioms className_go_eigen
#print axioms namesOk
#print axioms className_old
end FreshModuleActual
end Ratchet.Denote
