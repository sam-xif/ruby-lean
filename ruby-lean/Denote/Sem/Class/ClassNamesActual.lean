import Denote.Sem.Class.ClassHeapActual
import RubyCore.Proof.NameGrowth

/-! Extend the existing named-growth argument to the actual attached metaclass.
Old walks reuse NameGrowth; only the two fresh ids need new fuel equations. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

theorem namesOk_freshGrow {h h' : Heap} (hg : ClsGrow h h') (hn : NamesOk h)
    (hb : ∀ k, h.objs.size ≤ k → ∀ cp, h'.classPayload? k = some cp →
      classOf h' (.ref k) < h'.objs.size ∧
        ∀ o, cp.attached = some o → o < h'.objs.size ∧ (h'.get o).klass < h'.objs.size)
    (hp : ∀ k, h.objs.size ≤ k →
      classPath.go h' (h'.objs.size + 1) k = classPath.go h' h'.objs.size k)
    (hc : ∀ k, h.objs.size ≤ k →
      className.go h' (h'.objs.size + 1) k = className.go h' h'.objs.size k) : NamesOk h' := by
  have hsize := hg.size
  have lift_bound {k : ObjId} (hk : k < h.objs.size) : k < h'.objs.size :=
    Nat.lt_of_lt_of_le hk hg.size
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k cp hcp
    by_cases hk : k < h.objs.size
    · rw [hg.payloadOld hk] at hcp
      simpa only [classOf, hg.get k hk] using lift_bound (hn.classOf k cp hcp)
    · exact (hb k (Nat.le_of_not_lt hk) cp hcp).1
  · intro k cp o hcp ha
    by_cases hk : k < h.objs.size
    · rw [hg.payloadOld hk] at hcp
      obtain ⟨ho, hklass⟩ := hn.attached k cp o hcp ha
      exact ⟨lift_bound ho, by rw [hg.get o ho]; exact lift_bound hklass⟩
    · exact (hb k (Nat.le_of_not_lt hk) cp hcp).2 o ha
  · intro k
    by_cases hk : k < h.objs.size
    · rw [classPath_go_old hg.get hn _ k hk, classPath_go_old hg.get hn _ k hk]
      by_cases hz : h'.objs.size = h.objs.size
      · rw [hz]; exact hn.paths k
      · rw [classPath_go_ge hn (fuel := h'.objs.size + 1) (by omega),
          classPath_go_ge hn (fuel := h'.objs.size) (by omega)]
    · exact hp k (Nat.le_of_not_lt hk)
  · intro k
    by_cases hk : k < h.objs.size
    · rw [className_go_old hg.size hg.get hn _ k hk, className_go_old hg.size hg.get hn _ k hk]
      by_cases hz : h'.objs.size = h.objs.size
      · rw [hz]; exact hn.names k
      · rw [className_go_ge hn (fuel := h'.objs.size + 1) (by omega),
          className_go_ge hn (fuel := h'.objs.size) (by omega)]
    · exact hc k (Nat.le_of_not_lt hk)

namespace FreshClassActual
variable {p : ObjId}

theorem classPath_go_class {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) (fuel : Nat) :
    classPath.go (heap m name e p) (fuel + 1) m.heap.objs.size = name := by
  simp [classPath.go, Heap.classPayload?, get_class hd, namedObject, hn]

theorem className_go_class {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) (fuel : Nat) :
    className.go (heap m name e p) (fuel + 1) m.heap.objs.size = name := by
  simp [className.go, Heap.classPayload?, get_class hd, namedObject, freshClassPayload,
    classPath, classPath_go_class hd hn]

theorem className_go_eigen {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) (fuel : Nat) :
    className.go (heap m name e p) (fuel + 2) (m.heap.objs.size + 1) =
      "#<Class:" ++ name ++ ">" := by
  rw [className.go]
  simp [Heap.classPayload?, get_eigen, attachedClassEigen,
    get_class hd, namedObject, className_go_class hd hn]
  rfl

theorem namesOk {m : Machine} {name : String} {e : ObjId}
    (hc : ChainsIn m.heap) (hn : NamesOk m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hne : name.isEmpty = false) :
    NamesOk (heap m name e p) := by
  have hm := namesOk_constSetIn hn m.lexicalNamespace name (.ref m.heap.objs.size)
  apply namesOk_freshGrow (grow hd) hm
  · intro k hk cp hp
    rw [hmid_size] at hk
    have hl : k < (heap m name e p).objs.size := by
      by_cases hbound : k < (heap m name e p).objs.size
      · exact hbound
      · rw [classPayload?_oob _ _ hbound] at hp
        cases hp
    rcases fresh_cases hk hl with rfl | rfl
    · simp only [Heap.classPayload?, get_class hd, namedObject] at hp
      cases hp
      refine ⟨?_, fun o ha => by cases ha⟩
      simp [classOf, get_class hd, size]
    · simp only [Heap.classPayload?, get_eigen, attachedClassEigen] at hp
      cases hp
      refine ⟨?_, ?_⟩
      · simp only [classOf, get_eigen, attachedClassEigen, size]
        exact Nat.lt_of_lt_of_le hc.boot.1 (Nat.le_add_right _ _)
      · intro o ha
        have heq : o = m.heap.objs.size := (Option.some.inj ha).symm
        subst o
        constructor
        · rw [size m name e]; exact Nat.lt_add_of_pos_right (by decide)
        · rw [get_class hd]
          exact Nat.lt_of_lt_of_le hc.boot.1 (by rw [size]; omega)
  · intro k hk
    rw [hmid_size] at hk
    by_cases hl : k < (heap m name e p).objs.size
    · rcases fresh_cases hk hl with rfl | rfl
      · simp only [size, classPath_go_class hd hne]
      · simp [size, classPath.go, Heap.classPayload?, get_eigen, attachedClassEigen]
    · have hz : 0 < (heap m name e p).objs.size := by rw [size]; omega
      obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hz)
      simp [hs, classPath.go, classPayload?_oob _ _ hl]
  · intro k hk
    rw [hmid_size] at hk
    by_cases hl : k < (heap m name e p).objs.size
    · rcases fresh_cases hk hl with rfl | rfl
      · simp only [size, className_go_class hd hne]
      · simp only [size, className_go_eigen hd hne]
    · have hz : 0 < (heap m name e p).objs.size := by rw [size]; omega
      obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hz)
      simp [hs, className.go, classPayload?_oob _ _ hl]

theorem className_old {m : Machine} {name : String} {e k : ObjId}
    (hn : NamesOk m.heap) (hd : m.lexicalNamespace < m.heap.objs.size)
    (hk : k < m.heap.objs.size) : className (heap m name e p) k = className m.heap k := by
  have hg := grow (name := name) (e := e) (p := p) hd
  rw [Proof.className_old hg.size hg.get
    (namesOk_constSetIn hn m.lexicalNamespace name (.ref m.heap.objs.size))
    (by rw [hmid_size]; exact hk)]
  exact className_constSetIn m.heap m.lexicalNamespace k name _

theorem classPath_class {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) :
    classPath (heap m name e p) m.heap.objs.size = name :=
  classPath_go_class hd hn _

theorem className_class {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) :
    className (heap m name e p) m.heap.objs.size = name :=
  className_go_class hd hn _

theorem className_eigen {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hn : name.isEmpty = false) :
    className (heap m name e p) (m.heap.objs.size + 1) = "#<Class:" ++ name ++ ">" := by
  simpa only [className, size] using className_go_eigen hd hn (m.heap.objs.size + 1)

#print axioms className_go_eigen
#print axioms namesOk
#print axioms className_old
end FreshClassActual
end Ratchet.Denote
