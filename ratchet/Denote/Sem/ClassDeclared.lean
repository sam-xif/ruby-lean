import Denote.Sem.ClassBases
import Denote.Sem.ClassCore

/-! Fresh registration preserves declarations about already-installed classes. Constructor
dispatch and both directions of named ancestry remain intact.
The new class is not inserted into the positive table by this transport lemma. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem module_old (ho : Boot.objectId < h.objs.size) {k : ObjId} (hk : k < h.objs.size) :
    ((h₁).classPayload? k).map (·.isModule) = (h.classPayload? k).map (·.isModule) := by
  rw [Proof.Judgment.freshClsHeap_cp_old ho hk]
  have hp := congrArg (Option.map Prod.snd)
    (Proof.clsName_constSetIn h Boot.objectId k name (.ref h.objs.size))
  simpa only [Option.map_map, Function.comp_def] using hp

variable {κ : Ctx} {m n : Machine}

theorem declared (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m) : DeclClassOk κ n := by
  intro c hmem k hk
  have hol := hc.boot.2.2.2.2
  obtain ⟨j, hj, _⟩ := hclasses c hmem
  have hj' := named (e := e) hol hn hj
  rw [← hh] at hj'
  have heq : j = k := Option.some.inj (hj'.symm.trans hk)
  subst k
  have hjl := named_live hj
  have hcl := Proof.ClsGrow.classOf_lt hc hjl
  obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := hp c hmem j hj
  refine ⟨?_, hcls, hmod, ?_, ?_, ?_⟩
  · rw [hh, Proof.Judgment.ancestors_old_freshC hc hs hjl]; exact hroot
  · rw [hh, module_old hol hjl]; exact hism
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
      · rw [hh, Proof.Judgment.ancestors_old_freshC hc hs hjl]; exact ha
    · intro cn k hk ha
      rw [hh, Proof.Judgment.ancestors_old_freshC hc hs hjl] at ha
      have hkl := Proof.ClsGrow.ancestors_mem_lt hc hjl k (List.contains_iff_mem.mp ha)
      rw [hh] at hk
      exact hneg cn k (named_old_back ho hkl hk) ha

#print axioms module_old
#print axioms declared
end Ratchet.Denote.FreshClass
