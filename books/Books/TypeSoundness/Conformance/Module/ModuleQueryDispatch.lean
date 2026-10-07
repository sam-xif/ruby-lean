import Books.TypeSoundness.Conformance.Module.ModuleDispatch
import Books.TypeSoundness.Conformance.Subclass.SubclassDispatch

/-! Map fresh module query lookup to an old source: the empty module head stays at
its previously absent id; its eigenclass inherits Module. Native prefixes stay guarded. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModule
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

def source (h : Heap) (k : ObjId) : ObjId :=
  if k = h.objs.size + 1 then Boot.moduleId else k

theorem source_old {k : ObjId} (hk : k < h.objs.size) : source h k = k := by
  simp only [source, if_neg (Nat.ne_of_lt (Nat.lt_succ_of_lt hk))]

theorem method_source (hc : ChainsIn h) (hs : Saturated h) (k : ObjId) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn h (source h k) mn := by
  by_cases he : k = h.objs.size + 1
  · subst k; simpa only [source, ite_true] using method_eigen (name := name) hc hs mn
  · simp only [source, if_neg he]
    by_cases hl : k < h.objs.size
    · exact method_old hc hs hl mn
    · by_cases hk : k = h.objs.size
      · subst k
        rw [method_fresh, FreshClass.method_nonclass (classPayload?_oob h _ (Nat.lt_irrefl _))]
      · rw [FreshClass.method_nonclass (freshModHeap_cp_oob (Nat.le_of_not_lt (not_lt_add_two hl hk he))),
          FreshClass.method_nonclass (classPayload?_oob h k hl)]

theorem shadow_before_source (hnames : NamesOk h) (hc : ChainsIn h) (hs : Saturated h)
    (hne : name.isEmpty = false) {mn : String}
    (hn : crubyClassDefines name mn = false) (hen : crubyClassDefines ("#<Class:" ++ name ++ ">") mn = false)
    (k owner : ObjId)
    (hold : Interp.crubyShadow h ((ancestors h (source h k)).takeWhile (· != owner)) mn = none) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn = none := by
  by_cases he : k = h.objs.size + 1
  · subst k
    simp only [source, ite_true] at hold
    rw [ancestors_fresh_e hc hs]
    apply FreshClass.shadow_cons
    · simp [className_fresh_e, Interp.nativeSingletonMethod, Interp.featureMethod,
        Interp.featureHas, Interp.libraryNamespace, freshModHeap_cp_e, hen]
    · rw [shadow_old hnames (fun j hj => ClsGrow.ancestors_mem_lt hc hc.boot.2.1 j ((List.takeWhile_sublist _).mem hj))]
      exact hold
  · simp only [source, if_neg he] at hold
    by_cases hl : k < h.objs.size
    · rw [shadow_before_old hnames hc hs hl]; exact hold
    · by_cases hk : k = h.objs.size
      · subst k
        rw [ancestors_fresh_k]
        apply FreshClass.shadow_cons
        · simp [className_fresh_k (q := name) (by simpa only [hne] using Bool.false_ne_true),
            Interp.nativeSingletonMethod, Interp.featureMethod, Interp.featureHas,
            Interp.libraryNamespace, freshModHeap_cp_k, hn]
        · rfl
      · have hp₀ := classPayload?_oob h k hl
        have hp₁ : (h₁).classPayload? k = none := freshModHeap_cp_oob (Nat.le_of_not_lt (not_lt_add_two hl hk he))
        have ha₀ : ancestors h k = [k] := by simp [ancestors, ancestors.go, hp₀]
        have ha₁ : ancestors h₁ k = [k] := by simp [ancestors, ancestors.go, hp₁]
        simp only [ha₀] at hold
        rw [ha₁]
        have hname : className h₁ k = className h k := by simp only [className, className.go, hp₀, hp₁]
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
end Checker.Soundness.FreshModule
