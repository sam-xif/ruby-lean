import Denote.Sem.ClassIdentity
import Denote.Sem.ClassShape
import Denote.Sem.RootNames

/-! Root-name transport and the complete named ancestry of a newly registered class. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem rootNames {h : Heap} {name : String} {e : ObjId}
    (hc : RootNames h) (hl : ConstRefsLive h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) :
    RootNames (freshClsHeap h Boot.objectId name name e) := by
  refine ⟨fun cn k hk => named (lt_size_of_classPayload ho) hn (hc.named cn k hk), ?_⟩
  intro cn k hk hr
  exact hc.only cn k (named_old_back ho (hc.live hl hr) hk) hr

theorem named_chain {h : Heap} {name : String} {e : ObjId}
    (hc : ClassReady h) (hs : Proof.Saturated h) (hr : RootNames h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) :
    (∀ cn ∈ name :: rootAncestors, ∃ k,
      classNamed? (freshClsHeap h Boot.objectId name name e) cn = some k ∧
      (ancestors (freshClsHeap h Boot.objectId name name e) h.objs.size).contains k = true) ∧
    (∀ cn k, classNamed? (freshClsHeap h Boot.objectId name name e) cn = some k →
      (ancestors (freshClsHeap h Boot.objectId name name e) h.objs.size).contains k = true →
      cn ∈ name :: rootAncestors) := by
  have shape := ordinary (name := name) (d := Boot.objectId) (q := name) (e := e) hc hs
  have roots := rootNames (e := e) hr hc.constRefs ho hn
  constructor
  · intro cn hcn
    rcases List.mem_cons.mp hcn with rfl | hcn
    · exact ⟨h.objs.size, classNamed_freshClass ho hc.chains.boot.2.2.2.2,
        by simp [shape.chain]⟩
    · have hm : cn ∈ rootNameIds.map (·.1) := hcn
      obtain ⟨⟨cn', k⟩, hrow, rfl⟩ := List.mem_map.mp hm
      have hk : k ∈ rootIds := by
        change k ∈ rootNameIds.map (·.2)
        exact List.mem_map.mpr ⟨(cn', k), hrow, rfl⟩
      refine ⟨k, roots.named cn' k hrow, ?_⟩
      rw [shape.chain]
      exact List.contains_iff_mem.mpr (List.mem_cons_of_mem _ hk)
  · intro cn k hk hanc
    rw [shape.chain] at hanc
    rcases List.mem_cons.mp (List.contains_iff_mem.mp hanc) with he | hm
    · subst k
      rw [named_fresh_only hc.constRefs hc.chains.boot.2.2.2.2 hk]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (roots.only cn k hk hm)

#print axioms rootNames
#print axioms named_chain
end Ratchet.Denote.FreshClass
