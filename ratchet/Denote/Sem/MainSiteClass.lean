import Denote.Sem.ClassCore
import Denote.Sem.ClassConstants

/-! Fresh classes leave the retained top-level receiver and its dispatch sites intact. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem mainSite {κ : Ctx} {h : Heap} {name : String} {e : ObjId}
    (site : MainSite κ h) (hc : ClassReady h) (hs : Proof.Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hn : constOwn h Boot.objectId name = none) (he : (h.get Boot.objectId).eigen = some e) :
    MainSite κ (freshClsHeap h Boot.objectId name name e) := by
  let h' := freshClsHeap h Boot.objectId name name e
  have hr := site.ready
  have hmain : Boot.mainId < h.objs.size := hr.live
  have hobj : (h.classPayload? Boot.objectId).isSome = true := hr.classLive
  have hm : h.classPayload? Boot.mainId = none := by
    simp only [Heap.classPayload?, show (h.get Boot.mainId).payload = .none from hr.payload]
  have hco := classOf_old (name := name) (e := e) hmain
  have hcl := Proof.ClsGrow.classOf_lt hc.chains hmain
  have hmo (n : String) : Interp.methodOn h' (classOf h' (.ref Boot.mainId)) n =
      Interp.methodOn h (classOf h (.ref Boot.mainId)) n := by
    rw [hco, method_old hc.chains hs hcl]
  have hl (k : ObjId) (hk : k < h.objs.size) (n : String) :
      lookup h' (.ref k) n = lookup h (.ref k) n := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hk,
      method_old hc.chains hs (Proof.ClsGrow.classOf_lt hc.chains hk)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_,
      nominal hc hs hb hn he hr.object, classPayload_live hr.classLive, ?_⟩
    · change Boot.mainId < h'.objs.size
      dsimp only [h']
      rw [Proof.Judgment.freshClsHeap_size]
      exact Nat.lt_of_lt_of_le hmain (Nat.le_add_right _ _)
    · change (h'.get Boot.mainId).payload = .none
      rw [get_old_nonclass hmain hm]; exact hr.payload
    · change ancestors h' (classOf h' (.ref Boot.mainId)) = _
      rw [hco, Proof.Judgment.ancestors_old_freshC hc.chains hs hcl]; exact hr.chain
    · change objectHookQuietB h' = true
      simpa only [objectHookQuietB, definitionHookQuietB, hl Boot.objectId hc.chains.boot.2.2.2.2]
        using (show objectHookQuietB h = true from hr.hook)
  · intro n hn o md hm
    exact site.names n hn o md (by rwa [hmo] at hm)
  · intro n hb hf
    exact (hl Boot.mainId hmain n).trans (site.bare n hb hf)
  · intro hf o md hm
    exact site.missing hf o md (by rwa [hmo] at hm)
  · intro n
    by_cases heq : n = name
    · subst n
      simp only [mainConstResolve, const_self (name := name) (e := e) hobj,
        constLookup_eq_own]; rfl
    · simpa only [mainConstResolve, const_own_old_other hc.chains.boot.2.2.2.2
        hc.chains.boot.2.2.2.2 heq, const_from_old_other hc.chains hs hc.chains.boot.2.2.2.2 heq,
        const_other hc.chains.boot.2.2.2.2 heq] using site.constants n

#print axioms mainSite
end Ratchet.Denote.FreshClass
