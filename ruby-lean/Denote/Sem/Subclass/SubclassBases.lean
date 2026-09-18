import Ratchet.Guards.SubclassGuards
import Denote.Sem.Subclass.SubclassNames

/-! Preserve builtin ancestry through both fresh heads. Only bases with an active
negative-answer guard require separation from the parent. Metaclass separation is retained
by the class site; the parent obligation is derived from static names and conformance. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

theorem builtinBase_static {base : ObjId} {ch : List String} (hb : (base, ch) ∈ builtinBases) :
    ch ∈ builtinChains := by
  change ch ∈ builtinBases.map Prod.snd
  exact List.mem_map.mpr ⟨(base, ch), hb, rfl⟩

theorem StateOk.subclass_parent_separate {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {parent : ObjId} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hp : classNamed? m.heap c.name = some parent) (hf : subclassBaseFrameB κ c.name = true)
    {base : ObjId} {ch : List String} (hb : (base, ch) ∈ builtinBases)
    (hn : isANoOk κ.wholeCls ch = true) : parent ≠ base := by
  have hg := List.all_eq_true.mp hf ch (builtinBase_static hb)
  simp only [hn, Bool.not_true, Bool.false_or] at hg
  cases hs : ancestors? κ.classes c.name with
  | none => simp only [hs] at hg; cases hg
  | some ns =>
    cases hh : ch.head? with
    | none => simp only [hs, hh] at hg; cases hg
    | some bn =>
      simp only [hs, hh, Bool.and_eq_true, Bool.not_eq_true'] at hg
      intro heq
      subst parent
      have hbn := ((hm.baseChains base ch hb).1 hg.1.1).1 bn hh
      obtain ⟨k, site⟩ := hm.classSites.of_class hc
      have hk := Option.some.inj (site.named.symm.trans hp)
      subst k
      obtain ⟨rest, hfront⟩ := classFrontB_sound site.front
      have hself : (ancestors m.heap base).contains base = true := by simp [hfront]
      have hmem := ((hm.declCls c hc base hp).2.2.2.2.2 ns hs hg.1.2).2 bn base hbn hself
      have htrue := List.contains_iff_mem.mpr hmem
      rw [hg.2] at htrue
      cases htrue

namespace Subclass
variable {κ : Ctx} {m n : Machine} {name q : String} {parent eParent : ObjId}

theorem baseChains (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hl : parent < m.heap.objs.size) (hel : eParent < m.heap.objs.size)
    (hparent : ∀ base ch, (base, ch) ∈ builtinBases → isANoOk κ.wholeCls ch = true → parent ≠ base)
    (hmeta : ∀ base ch, (base, ch) ∈ builtinBases → eParent ≠ base)
    (hh : n.heap = heap m.heap Boot.objectId name q parent eParent) (hp : BaseChainsOk κ m) :
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
      · rw [hh, ancestors_old hc.chains hs hbl]; exact ha
  · intro hfree
    obtain ⟨hnames, hexact⟩ := hneg hfree
    refine ⟨?_, ?_⟩
    · intro cn j hbound hj ha
      rw [hh, ancestors_old hc.chains hs hbl] at ha
      have hjl := ClsGrow.ancestors_mem_lt hc.chains hbl j (List.contains_iff_mem.mp ha)
      rw [hh] at hj
      exact hnames cn j hbound (named_old_back ho hjl hj) ha
    · intro k hk
      rw [hh] at hk
      by_cases hkold : k < m.heap.objs.size
      · rw [ancestors_old hc.chains hs hkold] at hk
        exact hexact k hk
      · by_cases hkc : k = m.heap.objs.size
        · subst k
          rw [ancestors_class hc.chains hs hl] at hk
          rcases List.mem_cons.mp (List.contains_iff_mem.mp hk) with hb | hb
          · exact False.elim ((Nat.ne_of_lt hbl) hb)
          · exact False.elim (hparent base ch hbase hfree
              (hexact parent (List.contains_iff_mem.mpr hb)))
        · by_cases hke : k = m.heap.objs.size + 1
          · subst k
            rw [ancestors_eigen hc.chains hs hel] at hk
            rcases List.mem_cons.mp (List.contains_iff_mem.mp hk) with hb | hb
            · exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hbl)) hb)
            · exact False.elim (hmeta base ch hbase (hexact eParent (List.contains_iff_mem.mpr hb)))
          · have hout := Nat.le_of_not_lt (not_lt_add_two hkold hkc hke)
            have hp₀ : (heap m.heap Boot.objectId name q parent eParent).classPayload? k = none := cp_oob hout
            have ha : ancestors (heap m.heap Boot.objectId name q parent eParent) k = [k] := by
              simp [ancestors, ancestors.go, hp₀]
            rw [ha] at hk
            have hb : base = k := by simpa only [List.mem_singleton] using List.contains_iff_mem.mp hk
            subst k
            exact False.elim (hkold hbl)

#print axioms baseChains
end Subclass
#print axioms StateOk.subclass_parent_separate
end Ratchet.Denote
