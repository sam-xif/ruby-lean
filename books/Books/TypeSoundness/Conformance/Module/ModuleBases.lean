import Books.TypeSoundness.Conformance.Module.ModuleNames

/-! Fresh module heads cannot become subclasses of builtin data bases. The ordinary
head is parentless; the eigenclass inherits Module, which is separate from those bases. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

namespace FreshModule
variable {κ : Ctx} {m n : Machine} {name : String}

theorem baseChains (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshModHeap m.heap Boot.objectId name name) (hp : BaseChainsOk κ m) :
    BaseChainsOk κ n := by
  intro base ch hbase
  have hbl := Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.chains.boot.2.2.2.1
  have hol := hc.chains.boot.2.2.2.2
  obtain ⟨hpos, hneg⟩ := hp base ch hbase
  refine ⟨?_, ?_⟩
  · intro hfree
    obtain ⟨hhead, hnames⟩ := hpos hfree
    refine ⟨?_, ?_⟩
    · intro bn hbn
      rw [hh]; exact named hol hn (hhead bn hbn)
    · intro cn hcn
      obtain ⟨j, hj, ha⟩ := hnames cn hcn
      refine ⟨j, ?_, ?_⟩
      · rw [hh]; exact named hol hn hj
      · rw [hh, ancestors_old_fresh hc.chains hs hbl]; exact ha
  · intro hfree
    obtain ⟨hnames, hexact⟩ := hneg hfree
    refine ⟨?_, ?_⟩
    · intro cn j hbound hj ha
      rw [hh, ancestors_old_fresh hc.chains hs hbl] at ha
      have hjl := ClsGrow.ancestors_mem_lt hc.chains hbl j (List.contains_iff_mem.mp ha)
      rw [hh] at hj
      exact hnames cn j hbound (named_old_back ho hjl hj) ha
    · intro k hk
      rw [hh] at hk
      by_cases hkold : k < m.heap.objs.size
      · rw [ancestors_old_fresh hc.chains hs hkold] at hk
        exact hexact k hk
      · by_cases hkc : k = m.heap.objs.size
        · subst k
          rw [ancestors_fresh_k] at hk
          have hb : base = m.heap.objs.size := by simpa using hk
          exact False.elim ((Nat.ne_of_lt hbl) hb)
        · by_cases hke : k = m.heap.objs.size + 1
          · subst k
            rw [ancestors_fresh_e hc.chains hs] at hk
            rcases List.mem_cons.mp (List.contains_iff_mem.mp hk) with hb | hb
            · exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hbl)) hb)
            · have hsep : Boot.moduleId ≠ base := by
                have hall := List.all_eq_true.mp
                  (by decide : builtinBases.all (fun p => decide (Boot.moduleId ≠ p.1)) = true)
                  (base, ch) hbase
                exact of_decide_eq_true hall
              exact False.elim (hsep (hexact Boot.moduleId (List.contains_iff_mem.mpr hb)))
          · have hout := Nat.le_of_not_lt (not_lt_add_two hkold hkc hke)
            have hp₀ : (freshModHeap m.heap Boot.objectId name name).classPayload? k = none := freshModHeap_cp_oob hout
            have ha : ancestors (freshModHeap m.heap Boot.objectId name name) k = [k] := by
              simp [ancestors, ancestors.go, hp₀]
            rw [ha] at hk
            have hb : base = k := by simpa only [List.mem_singleton] using List.contains_iff_mem.mp hk
            subst k
            exact False.elim (hkold hbl)

#print axioms baseChains
end FreshModule
end Checker.Soundness
