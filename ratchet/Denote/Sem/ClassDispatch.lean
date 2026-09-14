import Denote.Sem.ClassHeap
import Denote.Sem.MethodHeap

/-! Dispatch after fresh class creation. Old chains stay fixed; the two fresh chains
inherit from Object and Object's eigenclass. Native-name shadow checks remain explicit. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem lookup_go_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    lookup.go h₁ mn ks = lookup.go h mn ks := by
  rw [Proof.ClsGrow.lookup_go_old Proof.Judgment.clsGrow_hmid_freshC ks
    (fun k hk => by rw [Proof.Judgment.hmid_size]; exact hl k hk)]
  exact Proof.lookup_go_constSetIn h Boot.objectId name _ mn ks

theorem method_old (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {k : ObjId} (hk : k < h.objs.size) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn h k mn := by
  rw [methodOn_eq_go, methodOn_eq_go, Proof.Judgment.ancestors_old_freshC hc hs hk,
    lookup_go_old (Proof.ClsGrow.ancestors_mem_lt hc hk)]

theorem method_class (hc : Proof.ChainsIn h) (hs : Proof.Saturated h) (mn : String) :
    Interp.methodOn h₁ h.objs.size mn = Interp.methodOn h Boot.objectId mn := by
  rw [methodOn_eq_go, Proof.Judgment.ancestors_freshC_k hc hs, lookup.go,
    Proof.Judgment.freshClsHeap_cp_k]
  change lookup.go h₁ mn (ancestors h Boot.objectId) = _
  rw [lookup_go_old (Proof.ClsGrow.ancestors_mem_lt hc hc.boot.2.2.2.2), methodOn_eq_go]

theorem method_eigen (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (he : e < h.objs.size) (mn : String) :
    Interp.methodOn h₁ (h.objs.size + 1) mn = Interp.methodOn h e mn := by
  rw [methodOn_eq_go, Proof.Judgment.ancestors_freshC_e hc hs he, lookup.go,
    Proof.Judgment.freshClsHeap_cp_e]
  change lookup.go h₁ mn (ancestors h e) = _
  rw [lookup_go_old (Proof.ClsGrow.ancestors_mem_lt hc he), methodOn_eq_go]

theorem method_nonclass {heap : Heap} {k : ObjId} (hp : heap.classPayload? k = none)
    (mn : String) : Interp.methodOn heap k mn = none := by
  simp [Interp.methodOn, ancestors, ancestors.go, hp, List.firstM]
  rfl

/-- The old dispatch site whose method table the new site inherits. -/
def parent (h : Heap) (e k : ObjId) : ObjId :=
  if k = h.objs.size then Boot.objectId else if k = h.objs.size + 1 then e else k

theorem parent_old {k : ObjId} (hk : k < h.objs.size) : parent h e k = k := by
  simp only [parent, if_neg (Nat.ne_of_lt hk), if_neg (Nat.ne_of_lt (Nat.lt_succ_of_lt hk))]

theorem method_parent (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (he : e < h.objs.size) (k : ObjId) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn h (parent h e k) mn := by
  by_cases hk : k = h.objs.size
  · subst k; simpa only [parent, ite_true] using method_class (name := name) (e := e) hc hs mn
  · by_cases he' : k = h.objs.size + 1
    · subst k
      simpa only [parent, if_neg (Nat.succ_ne_self _), ite_true] using method_eigen (name := name) hc hs he mn
    · simp only [parent, if_neg hk, if_neg he']
      by_cases hl : k < h.objs.size
      · exact method_old hc hs hl mn
      · have ho := Nat.le_of_not_lt (Proof.Judgment.not_lt_add_two hl hk he')
        rw [method_nonclass (Proof.Judgment.freshClsHeap_cp_oob ho),
          method_nonclass (Proof.classPayload?_oob h k hl)]

theorem shadow_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    Interp.crubyShadow h₁ ks mn = Interp.crubyShadow h ks mn := by
  rw [Proof.ClsGrow.crubyShadow_old Proof.Judgment.clsGrow_hmid_freshC ks
    (fun k hk => by rw [Proof.Judgment.hmid_size]; exact hl k hk)]
  simp only [Interp.crubyShadow, Proof.className_constSetIn]

theorem shadow_before_old (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {k : ObjId} (hk : k < h.objs.size) (owner : ObjId) (mn : String) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn =
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) mn := by
  rw [Proof.Judgment.ancestors_old_freshC hc hs hk]
  exact shadow_old (fun j hj => Proof.ClsGrow.ancestors_mem_lt hc hk j
    ((List.takeWhile_sublist _).mem hj)) mn

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

/-- Fresh class names must not introduce an unmodeled native method before the old owner. -/
theorem shadow_before_parent (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (he : e < h.objs.size) (hne : name.isEmpty = false) {mn : String}
    (hn : crubyClassDefines name mn = false)
    (hen : crubyClassDefines ("#<Class:" ++ name ++ ">") mn = false)
    (k owner : ObjId)
    (hp : Interp.crubyShadow h ((ancestors h (parent h e k)).takeWhile (· != owner)) mn = none) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn = none := by
  by_cases hk : k = h.objs.size
  · subst k
    simp only [parent, ite_true] at hp
    rw [Proof.Judgment.ancestors_freshC_k hc hs]
    apply shadow_cons
    · have hq : ¬ name.isEmpty = true := by rw [hne]; decide
      rw [Proof.Judgment.className_freshC_k hq]; exact hn
    · rw [shadow_old (fun j hj => Proof.ClsGrow.ancestors_mem_lt hc hc.boot.2.2.2.2 j
        ((List.takeWhile_sublist _).mem hj))]; exact hp
  · by_cases hek : k = h.objs.size + 1
    · subst k
      simp only [parent, if_neg (Nat.succ_ne_self _), ite_true] at hp
      rw [Proof.Judgment.ancestors_freshC_e hc hs he]
      apply shadow_cons
      · simpa only [Proof.Judgment.className_freshC_e] using hen
      · rw [shadow_old (fun j hj => Proof.ClsGrow.ancestors_mem_lt hc he j
          ((List.takeWhile_sublist _).mem hj))]; exact hp
    · simp only [parent, if_neg hk, if_neg hek] at hp
      by_cases hl : k < h.objs.size
      · rw [shadow_before_old hc hs hl]; exact hp
      · have ho := Nat.le_of_not_lt (Proof.Judgment.not_lt_add_two hl hk hek)
        have hp₀ := Proof.classPayload?_oob h k hl
        have hp₁ : (h₁).classPayload? k = none := Proof.Judgment.freshClsHeap_cp_oob ho
        have ha₀ : ancestors h k = [k] := by simp [ancestors, ancestors.go, hp₀]
        have ha₁ : ancestors h₁ k = [k] := by simp [ancestors, ancestors.go, hp₁]
        simp only [ha₀] at hp
        rw [ha₁]
        have hname : className h₁ k = className h k := by simp only [className, hp₀, hp₁]
        by_cases hko : k = owner
        · subst owner
          simp only [List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true,
            ite_false, Interp.crubyShadow, List.firstM]
          rfl
        · have hkb : (k != owner) = true := by simpa only [bne_iff_ne] using hko
          simpa only [List.takeWhile_cons, hkb, ite_true, List.takeWhile_nil, Interp.crubyShadow,
            List.firstM, hname] using hp

#print axioms method_parent
#print axioms shadow_before_parent
end Ratchet.Denote.FreshClass
