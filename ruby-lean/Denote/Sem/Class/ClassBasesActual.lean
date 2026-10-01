import Denote.Sem.Class.ClassDeclaredActual

/-! Retain the original builtin-chain positive/negative split for the actual two heads. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {κ : Ctx} {m n : Machine} {name : String} {e : ObjId}

theorem baseChains (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hh : n.heap = heap m name e) (hp : BaseChainsOk κ m) : BaseChainsOk κ n := by
  have hol := hc.chains.boot.2.2.2.2
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hol
  have hel := hc.chains.eigen _ hol _ he
  intro base ch hbase
  have hbl := Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.chains.boot.2.2.2.1
  obtain ⟨hpos, hneg⟩ := hp base ch hbase
  refine ⟨?_, ?_⟩
  · intro hfree
    obtain ⟨hhead, hnames⟩ := hpos hfree
    refine ⟨?_, ?_⟩
    · intro bn hbn
      rw [hh]; exact named_old htop hol hn (hhead bn hbn)
    · intro cn hcn
      obtain ⟨j, hj, ha⟩ := hnames cn hcn
      refine ⟨j, ?_, ?_⟩
      · rw [hh]; exact named_old htop hol hn hj
      · rw [hh, ancestors_old hc.chains hs hd hbl]; exact ha
  · intro hfree
    obtain ⟨hnames, hexact⟩ := hneg hfree
    refine ⟨?_, ?_⟩
    · intro cn j hbound hj ha
      rw [hh, ancestors_old hc.chains hs hd hbl] at ha
      have hjl := ClsGrow.ancestors_mem_lt hc.chains hbl j (List.contains_iff_mem.mp ha)
      rw [hh] at hj
      exact hnames cn j hbound (named_old_back htop ho hjl hj) ha
    · intro k hk
      rw [hh] at hk
      by_cases hkold : k < m.heap.objs.size
      · rw [ancestors_old hc.chains hs hd hkold] at hk
        exact hexact k hk
      · by_cases hkc : k = m.heap.objs.size
        · subst k
          rw [ancestors_class hc.chains hs hd] at hk
          rcases List.mem_cons.mp (List.contains_iff_mem.mp hk) with hb | hb
          · exact False.elim ((Nat.ne_of_lt hbl) hb)
          · exact False.elim ((builtinBase_bound hbase).2.symm
              (hexact Boot.objectId (List.contains_iff_mem.mpr hb)))
        · by_cases hke : k = m.heap.objs.size + 1
          · subst k
            rw [ancestors_eigen hc.chains hs hd hel] at hk
            rcases List.mem_cons.mp (List.contains_iff_mem.mp hk) with hb | hb
            · exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hbl)) hb)
            · exact False.elim (hc.eigenSeparate e he base ch hbase
                (hexact e (List.contains_iff_mem.mpr hb)))
          · have hout : ¬ k < (heap m name e).objs.size := by
              rw [size]; exact not_lt_add_two hkold hkc hke
            have hp₀ := RubyCore.Proof.classPayload?_oob (heap m name e) k hout
            have ha : ancestors (heap m name e) k = [k] := by
              simp [ancestors, ancestors.go, hp₀]
            rw [ha] at hk
            have hb : base = k := by simpa only [List.mem_singleton] using List.contains_iff_mem.mp hk
            subst k
            exact False.elim (hkold hbl)

#print axioms baseChains
end Ratchet.Denote.FreshClassActual
