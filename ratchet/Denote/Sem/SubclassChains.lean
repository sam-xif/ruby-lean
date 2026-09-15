import Denote.Sem.SubclassHeap

/-! Cached-parent subclass chains: old walks stay fixed, and each fresh owner prefixes
the corresponding old chain. The class and metaclass share one generic fresh-head proof. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

theorem ancestors_new_head {h h' : Heap} {k parent : ObjId}
    (hg : ClsGrow h h') (hc : ChainsIn h) (hs : Saturated h)
    (hz : h.objs.size + 1 ≤ h'.objs.size) (hk : h.objs.size ≤ k) (hp : parent < h.objs.size)
    (hstep : ∀ f, ancestors.go h' k (f + 1) = k :: ancestors.go h' parent f) :
    ancestors h' k = k :: ancestors h parent := by
  unfold ancestors
  rw [hstep, ClsGrow.ancestors_go_old hg hc hs _ parent hp, ancestors_go_ge hs.2 hz parent]
  have hne : ∀ x ∈ ancestors.go h parent (h.objs.size + 1), x ≠ k := by
    intro x hx he
    have hl := ClsGrow.ancestors_go_mem_lt hc _ parent hp x hx
    subst x
    exact Nat.not_lt_of_ge hk hl
  change List.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) [k]
    (ancestors.go h parent (h.objs.size + 1)) = _
  rw [foldl_dedup_cons hne [] (by simp)]

namespace Subclass

theorem grow {h : Heap} {d parent eParent : ObjId} {name q : String} :
    ClsGrow (hmidOf h d name) (heap h d name q parent eParent) :=
  ⟨by rw [size, hmid_size]; omega,
    fun o ho => get_old (by rwa [hmid_size] at ho)⟩

theorem ancestors_old {h : Heap} {d parent eParent k : ObjId} {name q : String}
    (hc : ChainsIn h) (hs : Saturated h) (hk : k < h.objs.size) :
    ancestors (heap h d name q parent eParent) k = ancestors h k := by
  rw [ClsGrow.ancestors_old grow (chainsIn_hmid hc) (saturated_hmid hs)
    (by rw [hmid_size]; exact hk)]
  exact ancestors_constSetIn h d k name _

theorem ancestors_class {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hc : ChainsIn h) (hs : Saturated h) (hp : parent < h.objs.size) :
    ancestors (heap h d name q parent eParent) h.objs.size = h.objs.size :: ancestors h parent := by
  have he := ancestors_new_head (h := hmidOf h d name) (h' := heap h d name q parent eParent)
    (k := h.objs.size) (parent := parent) grow
    (chainsIn_hmid (d := d) (name := name) hc) (saturated_hmid hs)
    (by rw [hmid_size, size]; omega) (by rw [hmid_size]; exact Nat.le_refl _) (by rw [hmid_size]; exact hp) (by
      intro f
      rw [ancestors.go.eq_def]
      simp only [Heap.classPayload?, get_class, classObjE, classObj]
      simp)
  rw [ancestors_constSetIn] at he
  exact he

theorem ancestors_eigen {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hc : ChainsIn h) (hs : Saturated h) (hp : eParent < h.objs.size) :
    ancestors (heap h d name q parent eParent) (h.objs.size + 1) =
      (h.objs.size + 1) :: ancestors h eParent := by
  have he := ancestors_new_head (h := hmidOf h d name) (h' := heap h d name q parent eParent)
    (k := h.objs.size + 1) (parent := eParent) grow
    (chainsIn_hmid (d := d) (name := name) hc) (saturated_hmid hs)
    (by rw [hmid_size, size]; omega) (by rw [hmid_size]; omega) (by rw [hmid_size]; exact hp) (by
      intro f
      rw [ancestors.go.eq_def]
      simp only [Heap.classPayload?, get_eigen, eigObjC]
      simp)
  rw [ancestors_constSetIn] at he
  exact he

#print axioms ancestors_class
#print axioms ancestors_eigen
end Subclass
end Ratchet.Denote
