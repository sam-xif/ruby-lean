import Denote.Sem.Subclass.SubclassData
import Denote.Sem.Instance.MethodHeap

/-! Dispatch from the two fresh sites reduces to the corresponding old parent.
The source map and native-prefix proof are shared with default-superclass creation. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

-- Parent-independent helpers retain their existing public names.
namespace FreshClass
theorem method_nonclass {heap : Heap} {k : ObjId} (hp : heap.classPayload? k = none)
    (mn : String) : Interp.methodOn heap k mn = none := by
  simp [Interp.methodOn, ancestors, ancestors.go, hp, List.firstM]
  rfl

theorem shadow_cons {heap : Heap} {k owner : ObjId} {ks : List ObjId} {mn : String}
    (hn : crubyClassDefines (className heap k) mn = false)
    (ht : Interp.crubyShadow heap (ks.takeWhile (· != owner)) mn = none) :
    Interp.crubyShadow heap ((k :: ks).takeWhile (· != owner)) mn = none := by
  by_cases hk : k != owner
  · simp only [List.takeWhile_cons, hk, ite_true, Interp.crubyShadow, List.firstM, hn,
      Bool.false_eq_true, ite_false]
    exact ht
  · simp only [List.takeWhile_cons, hk, Bool.false_eq_true, ite_false, Interp.crubyShadow, List.firstM]
    rfl
end FreshClass

namespace Subclass
variable {h : Heap} {d parent eParent : ObjId} {name q : String}
local notation "h₁" => heap h d name q parent eParent

theorem lookup_go_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    lookup.go h₁ mn ks = lookup.go h mn ks := by
  rw [ClsGrow.lookup_go_old grow ks (fun k hk => by rw [hmid_size]; exact hl k hk)]
  exact lookup_go_constSetIn h d name _ mn ks

theorem method_old (hc : ChainsIn h) (hs : Saturated h) {k : ObjId}
    (hk : k < h.objs.size) (mn : String) : Interp.methodOn h₁ k mn = Interp.methodOn h k mn := by
  rw [methodOn_eq_go, methodOn_eq_go, ancestors_old hc hs hk,
    lookup_go_old (ClsGrow.ancestors_mem_lt hc hk)]

theorem method_class (hc : ChainsIn h) (hs : Saturated h) (hp : parent < h.objs.size) (mn : String) :
    Interp.methodOn h₁ h.objs.size mn = Interp.methodOn h parent mn := by
  rw [methodOn_eq_go, ancestors_class hc hs hp, lookup.go]
  simp only [Heap.classPayload?, get_class, classObjE]
  change lookup.go h₁ mn (ancestors h parent) = _
  rw [lookup_go_old (ClsGrow.ancestors_mem_lt hc hp), methodOn_eq_go]

theorem method_eigen (hc : ChainsIn h) (hs : Saturated h) (he : eParent < h.objs.size) (mn : String) :
    Interp.methodOn h₁ (h.objs.size + 1) mn = Interp.methodOn h eParent mn := by
  rw [methodOn_eq_go, ancestors_eigen hc hs he, lookup.go]
  simp only [Heap.classPayload?, get_eigen, eigObjC]
  change lookup.go h₁ mn (ancestors h eParent) = _
  rw [lookup_go_old (ClsGrow.ancestors_mem_lt hc he), methodOn_eq_go]

def source (h : Heap) (parent eParent k : ObjId) : ObjId :=
  if k = h.objs.size then parent else if k = h.objs.size + 1 then eParent else k

theorem source_old {k : ObjId} (hk : k < h.objs.size) : source h parent eParent k = k := by
  simp only [source, if_neg (Nat.ne_of_lt hk), if_neg (Nat.ne_of_lt (Nat.lt_succ_of_lt hk))]

theorem method_source (hc : ChainsIn h) (hs : Saturated h)
    (hp : parent < h.objs.size) (he : eParent < h.objs.size) (k : ObjId) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn h (source h parent eParent k) mn := by
  by_cases hk : k = h.objs.size
  · subst k; simpa only [source, ite_true] using method_class (d := d) (name := name) (q := q) (eParent := eParent) hc hs hp mn
  · by_cases hek : k = h.objs.size + 1
    · subst k
      simpa only [source, if_neg (Nat.succ_ne_self _), ite_true] using
        method_eigen (d := d) (name := name) (q := q) (parent := parent) hc hs he mn
    · simp only [source, if_neg hk, if_neg hek]
      by_cases hl : k < h.objs.size
      · exact method_old hc hs hl mn
      · rw [FreshClass.method_nonclass (cp_oob (Nat.le_of_not_lt (not_lt_add_two hl hk hek))),
          FreshClass.method_nonclass (classPayload?_oob h k hl)]

theorem shadow_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    Interp.crubyShadow h₁ ks mn = Interp.crubyShadow h ks mn := by
  rw [ClsGrow.crubyShadow_old grow ks (fun k hk => by rw [hmid_size]; exact hl k hk)]
  simp only [Interp.crubyShadow, className_constSetIn]

theorem shadow_before_old (hc : ChainsIn h) (hs : Saturated h) {k : ObjId}
    (hk : k < h.objs.size) (owner : ObjId) (mn : String) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn =
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) mn := by
  rw [ancestors_old hc hs hk]
  exact shadow_old (fun j hj => ClsGrow.ancestors_mem_lt hc hk j ((List.takeWhile_sublist _).mem hj)) mn

theorem shadow_before_source (hc : ChainsIn h) (hs : Saturated h)
    (hp : parent < h.objs.size) (he : eParent < h.objs.size) (hne : q.isEmpty = false) {mn : String}
    (hn : crubyClassDefines q mn = false) (hen : crubyClassDefines ("#<Class:" ++ q ++ ">") mn = false)
    (k owner : ObjId)
    (hold : Interp.crubyShadow h ((ancestors h (source h parent eParent k)).takeWhile (· != owner)) mn = none) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn = none := by
  by_cases hk : k = h.objs.size
  · subst k
    simp only [source, ite_true] at hold
    rw [ancestors_class hc hs hp]
    apply FreshClass.shadow_cons
    · rw [className_class hne]; exact hn
    · rw [shadow_old (fun j hj => ClsGrow.ancestors_mem_lt hc hp j ((List.takeWhile_sublist _).mem hj))]
      exact hold
  · by_cases hek : k = h.objs.size + 1
    · subst k
      simp only [source, if_neg (Nat.succ_ne_self _), ite_true] at hold
      rw [ancestors_eigen hc hs he]
      apply FreshClass.shadow_cons
      · rw [className_eigen]; exact hen
      · rw [shadow_old (fun j hj => ClsGrow.ancestors_mem_lt hc he j ((List.takeWhile_sublist _).mem hj))]
        exact hold
    · simp only [source, if_neg hk, if_neg hek] at hold
      by_cases hl : k < h.objs.size
      · rw [shadow_before_old hc hs hl]; exact hold
      · have hp₀ := classPayload?_oob h k hl
        have hp₁ : (h₁).classPayload? k = none := cp_oob (Nat.le_of_not_lt (not_lt_add_two hl hk hek))
        have ha₀ : ancestors h k = [k] := by simp [ancestors, ancestors.go, hp₀]
        have ha₁ : ancestors h₁ k = [k] := by simp [ancestors, ancestors.go, hp₁]
        simp only [ha₀] at hold
        rw [ha₁]
        have hname : className h₁ k = className h k := by simp only [className, hp₀, hp₁]
        by_cases hko : k = owner
        · subst owner
          simp only [List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true,
            ite_false, Interp.crubyShadow, List.firstM]
          rfl
        · have hkb : (k != owner) = true := by simpa only [bne_iff_ne] using hko
          simpa only [List.takeWhile_cons, hkb, ite_true, List.takeWhile_nil, Interp.crubyShadow,
            List.firstM, hname] using hold

#print axioms method_source
#print axioms shadow_before_source
end Subclass
end Ratchet.Denote
