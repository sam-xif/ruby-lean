import Denote.Sem.Subclass.SubclassMethods
import Denote.Sem.Subclass.SubclassDispatch
import Denote.Sem.Names.OwnNames
import Denote.Sem.Class.ClassChains

/-! Preserve previously published class declarations, exact chains and own-selector bounds
through arbitrary fresh subclass registration. No new class/body is published here. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name q : String} {parent eParent : ObjId}
local notation "h₁" => heap h Boot.objectId name q parent eParent

theorem module_old {k : ObjId} (hk : k < h.objs.size) :
    ((h₁).classPayload? k).map (·.isModule) = (h.classPayload? k).map (·.isModule) := by
  rw [grow.payloadOld (by rwa [hmid_size])]
  have hp := congrArg (Option.map Prod.snd)
    (clsName_constSetIn h Boot.objectId k name (.ref h.objs.size))
  simpa only [Option.map_map, Function.comp_def] using hp

variable {κ : Ctx} {m n : Machine}

theorem declared (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = heap m.heap Boot.objectId name q parent eParent)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m) : DeclClassOk κ n := by
  intro c hmem k hk
  have hol := hc.boot.2.2.2.2
  obtain ⟨j, hj, _⟩ := hclasses c hmem
  have hj' := named (q := q) (parent := parent) (eParent := eParent) hol hn hj
  rw [← hh] at hj'
  have heq : j = k := Option.some.inj (hj'.symm.trans hk)
  subst k
  have hjl := named_live hj
  have hcl := ClsGrow.classOf_lt hc hjl
  obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := hp c hmem j hj
  refine ⟨?_, hcls, hmod, ?_, ?_, ?_⟩
  · rw [hh, ancestors_old hc hs hjl]; exact hroot
  · rw [hh, module_old hjl]; exact hism
  · intro hnone
    obtain ⟨hfound, hmiss⟩ := hnew hnone
    refine ⟨?_, ?_⟩
    · intro owner md hm
      rw [hh, classOf_old hjl, method_old hc hs hcl] at hm
      obtain ⟨hb, hu, hv, hpre, hshadow⟩ := hfound owner md hm
      refine ⟨hb, hu, hv, hpre, ?_⟩
      rw [hh, classOf_old hjl, shadow_before_old hc hs hcl]
      exact hshadow
    · intro hm owner md hf
      rw [hh, classOf_old hjl, method_old hc hs hcl] at hm hf
      exact hmiss hm owner md hf
  · intro ch hch hmix
    obtain ⟨hpos, hneg⟩ := hchain ch hch hmix
    refine ⟨?_, ?_⟩
    · intro cn hcn
      obtain ⟨k, hk, ha⟩ := hpos cn hcn
      refine ⟨k, ?_, ?_⟩
      · rw [hh]; exact named hol hn hk
      · rw [hh, ancestors_old hc hs hjl]; exact ha
    · intro cn k hk ha
      rw [hh, ancestors_old hc hs hjl] at ha
      have hkl := ClsGrow.ancestors_mem_lt hc hjl k (List.contains_iff_mem.mp ha)
      rw [hh] at hk
      exact hneg cn k (named_old_back ho hkl hk) ha

theorem ownNames {C : CTable}
    (ho : Boot.objectId < m.heap.objs.size) (hn : constOwn m.heap Boot.objectId name = none)
    (hc : ClassesOk C m) (hp : ClassOwnNames C m.heap) :
    ClassOwnNames C (heap m.heap Boot.objectId name q parent eParent) := by
  apply hp.transport
  · intro c hmem k hk
    obtain ⟨j, hj, _⟩ := hc c hmem
    have he := (named (q := q) (parent := parent) (eParent := eParent) ho hn hj).symm.trans hk
    exact Option.some.inj he ▸ hj
  · intro k p hm
    simpa only [ownMethods, own_methods] using hm

theorem classChains {C : CTable} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassChains C m.heap) :
    ClassChains C (heap m.heap Boot.objectId name q parent eParent) := by
  intro c hmem k hk ns hns
  obtain ⟨j, hj, _⟩ := ht c hmem
  have he := (named (q := q) (parent := parent) (eParent := eParent) hc.chains.boot.2.2.2.2 hn hj).symm.trans hk
  have heq := Option.some.inj he
  subst k
  rw [ancestors_old hc.chains hs (named_live hj)]
  exact (hp c hmem j hj ns hns).names (fun _ _ hj => named hc.chains.boot.2.2.2.2 hn hj)

#print axioms declared
#print axioms ownNames
#print axioms classChains
end Ratchet.Denote.Subclass
