import Denote.Sem.ClassHeap

/-! Fresh default-superclass declarations preserve builtin ancestry answers. The new
metaclass inherits Object's eigenclass, whose identity must be separate from the bases. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

/-- A name resolving to an old class after registration already resolved there before.
Names that held dangling references may acquire a new meaning, but only at a fresh id. -/
theorem named_old_back (ho : (h.classPayload? Boot.objectId).isSome = true)
    {cn : String} {j : ObjId} (hj : j < h.objs.size) (hk : classNamed? h₁ cn = some j) :
    classNamed? h cn = some j := by
  have hol := lt_size_of_classPayload ho
  by_cases hcn : cn = name
  · subst cn
    rw [classNamed_freshClass ho hol] at hk
    exact False.elim ((Nat.ne_of_lt hj) (Option.some.inj hk).symm)
  · unfold classNamed? at hk ⊢
    rw [const_other hol hcn] at hk
    split at hk
    · rename_i o hl
      split at hk
      · rename_i hp
        cases hk
        have hp₀ : (h.classPayload? j).isSome = true := by
          rw [← classPayload_old_isSome (name := name) (e := e) hj]; exact hp
        simp only [hp₀, ite_true]
      · cases hk
    · cases hk

variable {κ : Ctx} {m n : Machine}

theorem baseChains (hc : ClassReady m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hp : BaseChainsOk κ m) :
    BaseChainsOk κ n := by
  intro base ch hbase
  have hbl := Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.chains.boot.2.2.2.1
  have hol := hc.chains.boot.2.2.2.2
  have hel := hc.chains.eigen Boot.objectId hol e he
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
      · rw [hh, Proof.Judgment.ancestors_old_freshC hc.chains hs hbl]; exact ha
  · intro hfree
    obtain ⟨hnames, hexact⟩ := hneg hfree
    refine ⟨?_, ?_⟩
    · intro cn j hbound hj ha
      rw [hh, Proof.Judgment.ancestors_old_freshC hc.chains hs hbl] at ha
      have hjl := Proof.ClsGrow.ancestors_mem_lt hc.chains hbl j (List.contains_iff_mem.mp ha)
      rw [hh] at hj
      exact hnames cn j hbound (named_old_back ho hjl hj) ha
    · intro k hk
      rw [hh] at hk
      by_cases hl : k < m.heap.objs.size
      · rw [Proof.Judgment.ancestors_old_freshC hc.chains hs hl] at hk
        exact hexact k hk
      · by_cases hkc : k = m.heap.objs.size
        · subst k
          rw [Proof.Judgment.ancestors_freshC_k hc.chains hs] at hk
          rcases List.mem_cons.mp (List.contains_iff_mem.mp hk) with hb | hb
          · exact False.elim ((Nat.ne_of_lt hbl) hb)
          · exact False.elim ((builtinBase_bound hbase).2
              (hexact Boot.objectId (List.contains_iff_mem.mpr hb)).symm)
        · by_cases hke : k = m.heap.objs.size + 1
          · subst k
            rw [Proof.Judgment.ancestors_freshC_e hc.chains hs hel] at hk
            rcases List.mem_cons.mp (List.contains_iff_mem.mp hk) with hb | hb
            · exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hbl)) hb)
            · exact False.elim (hc.eigenSeparate e he base ch hbase
                (hexact e (List.contains_iff_mem.mpr hb)))
          · have hout := Nat.le_of_not_lt (Proof.Judgment.not_lt_add_two hl hkc hke)
            have hp₀ : (freshClsHeap m.heap Boot.objectId name name e).classPayload? k = none :=
              Proof.Judgment.freshClsHeap_cp_oob hout
            have ha : ancestors (freshClsHeap m.heap Boot.objectId name name e) k = [k] := by
              simp [ancestors, ancestors.go, hp₀]
            rw [ha] at hk
            have hb : base = k := by simpa only [List.mem_singleton] using List.contains_iff_mem.mp hk
            subst k
            exact False.elim (hl hbl)

#print axioms named_old_back
#print axioms baseChains
end Ratchet.Denote.FreshClass
