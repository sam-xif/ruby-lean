import Books.TypeSoundness.Conformance.Module.ModuleNames
import Books.TypeSoundness.Conformance.Instance.MethodHeap

/-! Old dispatch and native-prefix observations survive module registration. Fresh
instance dispatch is empty; the fresh eigenclass dispatches through Module. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModule
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem lookup_go_old (hc : ChainsIn h) (hs : Saturated h) {ks : List ObjId}
    (hl : ∀ k ∈ ks, k < h.objs.size) (hlen : ks.length ≤ h.objs.size + 1) (mn : String) :
    lookupInChain h₁ ks mn = lookupInChain h ks mn := by
  rw [ClsGrow.lookup_go_old clsGrow_hmid_fresh (chainsIn_hmid hc) (saturated_hmid hs)
    ks (fun k hk => by rw [hmid_size]; exact hl k hk) (by rw [hmid_size]; exact hlen)]
  exact lookup_go_constSetIn h Boot.objectId name _ mn ks

theorem method_old (hc : ChainsIn h) (hs : Saturated h) {k : ObjId}
    (hk : k < h.objs.size) (mn : String) : Interp.methodOn h₁ k mn = Interp.methodOn h k mn := by
  rw [methodOn_eq_go, methodOn_eq_go, ancestors_old_fresh hc hs hk,
    lookup_go_old hc hs (ClsGrow.ancestors_mem_lt hc hk) (ancestors_length_bound hc k)]

theorem method_fresh (mn : String) : Interp.methodOn h₁ h.objs.size mn = none := by
  rw [methodOn_eq_go, ancestors_fresh_k]
  simp [lookupInChain, lookupInChain.go, freshModHeap_cp_k]

theorem method_eigen (hc : ChainsIn h) (hs : Saturated h) (mn : String) :
    Interp.methodOn h₁ (h.objs.size + 1) mn = Interp.methodOn h Boot.moduleId mn := by
  have ho := ancestors_length_bound hc Boot.objectId
  have hm := ancestors_length_bound hc Boot.moduleId
  have ha : ancestors h₁ Boot.objectId = ancestors h Boot.objectId :=
    ancestors_old_fresh hc hs hc.boot.2.2.2.2
  rw [methodOn_eq_go, ancestors_fresh_e hc hs,
    lookupInChain_eq_scan _ _ _ (by rw [List.length_cons, ha, freshModHeap_size]; omega)]
  simp only [lookupScan, freshModHeap_cp_e, List.find?_nil]
  rw [← lookupInChain_eq_scan _ _ _ (by rw [ha, freshModHeap_size]; omega),
    lookup_go_old hc hs (ClsGrow.ancestors_mem_lt hc hc.boot.2.1) hm]
  rfl

theorem shadow_old (hn : NamesOk h) {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    Interp.crubyShadow h₁ ks mn = Interp.crubyShadow h ks mn := by
  rw [ClsGrow.crubyShadow_old clsGrow_hmid_fresh (namesOk_constSetIn hn _ _ _) ks (fun k hk => by rw [hmid_size]; exact hl k hk)]
  exact crubyShadow_constSetIn ks mn

theorem shadow_before_old (hn : NamesOk h) (hc : ChainsIn h) (hs : Saturated h) {k : ObjId}
    (hk : k < h.objs.size) (owner : ObjId) (mn : String) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn =
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) mn := by
  rw [ancestors_old_fresh hc hs hk]
  exact shadow_old hn (fun j hj => ClsGrow.ancestors_mem_lt hc hk j ((List.takeWhile_sublist _).mem hj)) mn

#print axioms method_eigen
#print axioms shadow_before_old
end Checker.Soundness.FreshModule
