import Denote.Sem.Module.ModuleNames
import Denote.Sem.Instance.MethodHeap

/-! Old dispatch and native-prefix observations survive module registration. Fresh
instance dispatch is empty; the fresh eigenclass dispatches through Module. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem lookup_go_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    lookup.go h₁ mn ks = lookup.go h mn ks := by
  rw [ClsGrow.lookup_go_old clsGrow_hmid_fresh ks (fun k hk => by rw [hmid_size]; exact hl k hk)]
  exact lookup_go_constSetIn h Boot.objectId name _ mn ks

theorem method_old (hc : ChainsIn h) (hs : Saturated h) {k : ObjId}
    (hk : k < h.objs.size) (mn : String) : Interp.methodOn h₁ k mn = Interp.methodOn h k mn := by
  rw [methodOn_eq_go, methodOn_eq_go, ancestors_old_fresh hc hs hk,
    lookup_go_old (ClsGrow.ancestors_mem_lt hc hk)]

theorem method_fresh (mn : String) : Interp.methodOn h₁ h.objs.size mn = none := by
  rw [methodOn_eq_go, ancestors_fresh_k, lookup.go, freshModHeap_cp_k]
  rfl

theorem method_eigen (hc : ChainsIn h) (hs : Saturated h) (mn : String) :
    Interp.methodOn h₁ (h.objs.size + 1) mn = Interp.methodOn h Boot.moduleId mn := by
  rw [methodOn_eq_go, ancestors_fresh_e hc hs, lookup.go, freshModHeap_cp_e]
  change lookup.go h₁ mn (ancestors h Boot.moduleId) = _
  rw [lookup_go_old (ClsGrow.ancestors_mem_lt hc hc.boot.2.1), methodOn_eq_go]

theorem shadow_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    Interp.crubyShadow h₁ ks mn = Interp.crubyShadow h ks mn := by
  rw [ClsGrow.crubyShadow_old clsGrow_hmid_fresh ks (fun k hk => by rw [hmid_size]; exact hl k hk)]
  simp only [Interp.crubyShadow, className_constSetIn]

theorem shadow_before_old (hc : ChainsIn h) (hs : Saturated h) {k : ObjId}
    (hk : k < h.objs.size) (owner : ObjId) (mn : String) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn =
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) mn := by
  rw [ancestors_old_fresh hc hs hk]
  exact shadow_old (fun j hj => ClsGrow.ancestors_mem_lt hc hk j ((List.takeWhile_sublist _).mem hj)) mn

#print axioms method_eigen
#print axioms shadow_before_old
end Ratchet.Denote.FreshModule
