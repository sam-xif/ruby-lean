import Denote.Sem.Module.ModuleCoreActual
import Denote.Sem.Class.ClassDispatchActual

/-! Dispatch at the actual module heap: the module's own lookup is empty; its
metaclass reproduces Module's lookup. -/


set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String} 
local notation "h₁" => heap m name

theorem lookup_go_old (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) {ks : List ObjId}
    (hl : ∀ k ∈ ks, k < m.heap.objs.size) (hlen : ks.length ≤ m.heap.objs.size + 1) (mn : String) :
    lookupInChain h₁ ks mn = lookupInChain m.heap ks mn := by
  rw [ClsGrow.lookup_go_old (grow hd) (chainsIn_hmid hc) (saturated_hmid hs)
    ks (fun k hk => by rw [hmid_size]; exact hl k hk) (by rw [hmid_size]; exact hlen)]
  exact lookup_go_constSetIn m.heap m.lexicalNamespace name _ mn ks

theorem method_old (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) {k : ObjId}
    (hk : k < m.heap.objs.size) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn m.heap k mn := by
  rw [methodOn_eq_go, methodOn_eq_go, ancestors_old hc hs hd hk,
    lookup_go_old hc hs hd (ClsGrow.ancestors_mem_lt hc hk) (ancestors_length_bound hc k)]

theorem method_module (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size) (mn : String) :
    Interp.methodOn h₁ m.heap.objs.size mn = none := by
  unfold Interp.methodOn
  rw [ancestors_module hc hd]
  unfold lookupInChain
  rw [size, show 2 * (m.heap.objs.size + 2) + 2 = (2 * m.heap.objs.size + 5) + 1 by omega]
  simp [lookupInChain.go, Heap.classPayload?, get_module hd, namedObject, modPayload]

theorem method_eigen (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (mn : String) :
    Interp.methodOn h₁ (m.heap.objs.size + 1) mn = Interp.methodOn m.heap Boot.moduleId mn := by
  have ha := ancestors_old (name := name) hc hs hd hc.boot.2.1
  have ha' := ancestors_old (name := name) hc hs hd hc.boot.2.2.2.2
  have ho := ancestors_length_bound hc Boot.objectId
  have hp := ancestors_length_bound hc Boot.moduleId
  rw [methodOn_eq_go, ancestors_eigen hc hs hd,
    lookupInChain_eq_scan _ _ _ (by simp only [List.length_cons, ha', size m name]; omega)]
  simp only [lookupScan, Heap.classPayload?, get_eigen, attachedModuleEigen, List.find?_nil]
  rw [← lookupInChain_eq_scan _ _ _ (by simp only [ha', size m name]; omega),
    lookup_go_old hc hs hd (ClsGrow.ancestors_mem_lt hc hc.boot.2.1) hp]
  rfl

/-- Old id whose lookup the new metaclass reproduces; the module itself has none. -/
def source (h : Heap) (k : ObjId) : ObjId := if k = h.objs.size + 1 then Boot.moduleId else k

theorem source_old {k : ObjId} (hk : k < m.heap.objs.size) : source m.heap k = k := by
  unfold source; rw [if_neg (Nat.ne_of_lt (Nat.lt_succ_of_lt hk))]

theorem method_source (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) {k : ObjId} (hk : k ≠ m.heap.objs.size) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn m.heap (source m.heap k) mn := by
  by_cases hek : k = m.heap.objs.size + 1
  · subst k
    simpa only [source, ite_true] using method_eigen (name := name) hc hs hd mn
  · simp only [source, if_neg hek]
    by_cases hl : k < m.heap.objs.size
    · exact method_old hc hs hd hl mn
    · rw [FreshClass.method_nonclass (classPayload?_oob _ _ (by
          rw [size m name]; exact not_lt_add_two hl hk hek)),
        FreshClass.method_nonclass (classPayload?_oob m.heap k hl)]

theorem shadow_old (hnames : NamesOk m.heap) (hd : m.lexicalNamespace < m.heap.objs.size)
    {ks : List ObjId} (hl : ∀ k ∈ ks, k < m.heap.objs.size) (mn : String) :
    Interp.crubyShadow h₁ ks mn = Interp.crubyShadow m.heap ks mn := by
  rw [ClsGrow.crubyShadow_old (grow hd) (namesOk_constSetIn hnames _ _ _) ks
    (fun k hk => by rw [hmid_size]; exact hl k hk)]
  exact crubyShadow_constSetIn ks mn

theorem shadow_before_old (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) {k : ObjId}
    (hk : k < m.heap.objs.size) (owner : ObjId) (mn : String) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn =
      Interp.crubyShadow m.heap ((ancestors m.heap k).takeWhile (· != owner)) mn := by
  rw [ancestors_old hc hs hd hk]
  exact shadow_old hnames hd (fun j hj => ClsGrow.ancestors_mem_lt hc hk j ((List.takeWhile_sublist _).mem hj)) mn

theorem shadow_before_source (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hne : name.isEmpty = false)
    {mn : String} (hen : crubyClassDefines ("#<Class:" ++ name ++ ">") mn = false)
    (hsingle : crubySingletonDefines name mn = false)
    (hlmain : Boot.mainId < m.heap.objs.size) {k : ObjId} (hk : k ≠ m.heap.objs.size) (owner : ObjId)
    (hold : Interp.crubyShadow m.heap ((ancestors m.heap (source m.heap k)).takeWhile (· != owner)) mn = none) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn = none := by
  have hmain : m.heap.objs.size ≠ Boot.mainId := (Nat.ne_of_lt hlmain).symm
  by_cases hek : k = m.heap.objs.size + 1
  · subst k
    simp only [source, ite_true] at hold
    rw [ancestors_eigen hc hs hd]
    apply FreshClass.shadow_cons
    · simp [className_eigen hd hne, Interp.nativeSingletonMethod, Interp.featureMethod,
        Interp.featureHas, Interp.libraryNamespace, Heap.classPayload?, get_eigen, attachedModuleEigen, hen,
        get_module hd, namedObject, modPayload, className_module hd hne, hsingle, hmain]
    · rw [shadow_old hnames hd (fun j hj => ClsGrow.ancestors_mem_lt hc hc.boot.2.1 j ((List.takeWhile_sublist _).mem hj))]
      exact hold
  · simp only [source, if_neg hek] at hold
    by_cases hl : k < m.heap.objs.size
    · rw [shadow_before_old hnames hc hs hd hl]; exact hold
    · have hp₀ := classPayload?_oob m.heap k hl
      have hp₁ : (h₁).classPayload? k = none := classPayload?_oob _ _ (by
        rw [size m name]; exact not_lt_add_two hl hk hek)
      have ha₀ : ancestors m.heap k = [k] := by simp [ancestors, ancestors.go, hp₀]
      have ha₁ : ancestors h₁ k = [k] := by simp [ancestors, ancestors.go, hp₁]
      simp only [ha₀] at hold
      rw [ha₁]
      have hname : className h₁ k = className m.heap k := by simp only [className, className.go, hp₀, hp₁]
      by_cases hko : k = owner
      · subst owner
        simp only [List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true,
          ite_false, Interp.crubyShadow, List.firstM]
        rfl
      · have hkb : (k != owner) = true := by simpa only [bne_iff_ne] using hko
        simpa only [List.takeWhile_cons, hkb, ite_true, List.takeWhile_nil, Interp.crubyShadow,
          List.firstM, hname, Interp.nativeSingletonMethod, Interp.featureMethod,
          Interp.featureHas, Interp.libraryNamespace, hp₀, hp₁, Option.bind_none,
          Option.any_none, Bool.or_false] using hold

#print axioms method_source
#print axioms shadow_before_source
end Ratchet.Denote.FreshModuleActual
