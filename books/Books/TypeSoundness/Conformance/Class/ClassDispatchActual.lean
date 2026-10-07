import Books.TypeSoundness.Conformance.Class.ClassDataActual
import Books.TypeSoundness.Conformance.Subclass.SubclassDispatch

/-! Retain the source-site dispatch argument for the actual attached heap. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {p : ObjId}
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e p

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

theorem method_class (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hpl : p < m.heap.objs.size) (mn : String) :
    Interp.methodOn h₁ m.heap.objs.size mn = Interp.methodOn m.heap p mn := by
  have ho := ancestors_length_bound hc Boot.objectId
  have hao := ancestors_old (name := name) (e := e) (p := p) hc hs hd hc.boot.2.2.2.2
  have hp := ancestors_length_bound hc p
  rw [methodOn_eq_go, ancestors_class hc hs hd hpl,
    lookupInChain_eq_scan _ _ _ (by rw [List.length_cons, hao, size m name e]; omega)]
  simp only [lookupScan, Heap.classPayload?, get_class hd, namedObject, freshClassPayload, List.find?_nil]
  rw [← lookupInChain_eq_scan _ _ _ (by rw [hao, size m name e]; omega),
    lookup_go_old hc hs hd (ClsGrow.ancestors_mem_lt hc hpl) hp]
  rfl

theorem method_eigen (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (he : e < m.heap.objs.size) (mn : String) :
    Interp.methodOn h₁ (m.heap.objs.size + 1) mn = Interp.methodOn m.heap e mn := by
  have ho := ancestors_length_bound hc Boot.objectId
  have ha := ancestors_old (name := name) (e := e) (p := p) hc hs hd hc.boot.2.2.2.2
  have hp := ancestors_length_bound hc e
  rw [methodOn_eq_go, ancestors_eigen hc hs hd he,
    lookupInChain_eq_scan _ _ _ (by rw [List.length_cons, ha, size m name e]; omega)]
  simp only [lookupScan, Heap.classPayload?, get_eigen, attachedClassEigen, List.find?_nil]
  rw [← lookupInChain_eq_scan _ _ _ (by rw [ha, size m name e]; omega),
    lookup_go_old hc hs hd (ClsGrow.ancestors_mem_lt hc he) hp]
  rfl

abbrev source (h : Heap) (e k : ObjId) (p : ObjId := Boot.objectId) : ObjId :=
  Subclass.source h p e k

theorem source_old {k : ObjId} (hk : k < m.heap.objs.size) :
    source m.heap e k p = k := Subclass.source_old hk

theorem method_source (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (he : e < m.heap.objs.size)
    (hpl : p < m.heap.objs.size) (k : ObjId) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn m.heap (source m.heap e k p) mn := by
  by_cases hk : k = m.heap.objs.size
  · subst k; simpa only [source, Subclass.source, ite_true] using method_class (name := name) (e := e) (p := p) hc hs hd hpl mn
  · by_cases hek : k = m.heap.objs.size + 1
    · subst k
      simpa only [source, Subclass.source, if_neg (Nat.succ_ne_self _), ite_true] using
        method_eigen (name := name) hc hs hd he mn
    · simp only [source, Subclass.source, if_neg hk, if_neg hek]
      by_cases hl : k < m.heap.objs.size
      · exact method_old hc hs hd hl mn
      · rw [FreshClass.method_nonclass (classPayload?_oob _ _ (by
            rw [size m name e]; exact not_lt_add_two hl hk hek)),
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
    (hd : m.lexicalNamespace < m.heap.objs.size) (he : e < m.heap.objs.size) (hne : name.isEmpty = false)
    {mn : String} (hn : crubyClassDefines name mn = false)
    (hen : crubyClassDefines ("#<Class:" ++ name ++ ">") mn = false)
    (hsingle : crubySingletonDefines name mn = false)
    (hlmain : Boot.mainId < m.heap.objs.size) (hpl : p < m.heap.objs.size) (k owner : ObjId)
    (hold : Interp.crubyShadow m.heap ((ancestors m.heap (source m.heap e k p)).takeWhile (· != owner)) mn = none) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn = none := by
  have hmain : m.heap.objs.size ≠ Boot.mainId :=
    (Nat.ne_of_lt hlmain).symm
  by_cases hk : k = m.heap.objs.size
  · subst k
    simp only [source, Subclass.source, ite_true] at hold
    rw [ancestors_class hc hs hd hpl]
    apply FreshClass.shadow_cons
    · simp [className_class hd hne, Interp.nativeSingletonMethod, Interp.featureMethod,
        Interp.featureHas, Interp.libraryNamespace, Heap.classPayload?, get_class hd, namedObject, freshClassPayload, hn]
    · rw [shadow_old hnames hd (fun j hj => ClsGrow.ancestors_mem_lt hc hpl j ((List.takeWhile_sublist _).mem hj))]
      exact hold
  · by_cases hek : k = m.heap.objs.size + 1
    · subst k
      simp only [source, Subclass.source, if_neg (Nat.succ_ne_self _), ite_true] at hold
      rw [ancestors_eigen hc hs hd he]
      apply FreshClass.shadow_cons
      · simp [className_eigen hd hne, Interp.nativeSingletonMethod, Interp.featureMethod,
          Interp.featureHas, Interp.libraryNamespace, Heap.classPayload?, get_eigen, attachedClassEigen, hen, get_class hd, namedObject, freshClassPayload,
          className_class hd hne, hsingle, hmain]
      · rw [shadow_old hnames hd (fun j hj => ClsGrow.ancestors_mem_lt hc he j ((List.takeWhile_sublist _).mem hj))]
        exact hold
    · simp only [source, Subclass.source, if_neg hk, if_neg hek] at hold
      by_cases hl : k < m.heap.objs.size
      · rw [shadow_before_old hnames hc hs hd hl]; exact hold
      · have hp₀ := classPayload?_oob m.heap k hl
        have hp₁ : (h₁).classPayload? k = none := classPayload?_oob _ _ (by
          rw [size m name e]; exact not_lt_add_two hl hk hek)
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
end Checker.Soundness.FreshClassActual
