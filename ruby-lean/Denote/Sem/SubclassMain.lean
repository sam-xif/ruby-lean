import Denote.Sem.SubclassCore
import Denote.Sem.SubclassConstants

/-! The retained main receiver and dispatch sites survive arbitrary subclass registration.
Data preservation supplies nominal retention; constants use the shared registration proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet

theorem mainSite {κ : Ctx} {h : Heap} {name q : String} {parent eParent : ObjId}
    (site : MainSite κ h) (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (hd : DataPres h (heap h Boot.objectId name q parent eParent)) :
    MainSite κ (heap h Boot.objectId name q parent eParent) := by
  let h' := heap h Boot.objectId name q parent eParent
  have hr := site.ready
  have hmain : Boot.mainId < h.objs.size := hr.live
  have hobj : (h.classPayload? Boot.objectId).isSome = true := hr.classLive
  have hm : h.classPayload? Boot.mainId = none := by
    simp only [Heap.classPayload?, show (h.get Boot.mainId).payload = .none from hr.payload]
  have hco := classOf_old (d := Boot.objectId) (name := name) (q := q) (parent := parent) (eParent := eParent) hmain
  have hcl := Proof.ClsGrow.classOf_lt hc hmain
  have hmo (n : String) : Interp.methodOn h' (classOf h' (.ref Boot.mainId)) n =
      Interp.methodOn h (classOf h (.ref Boot.mainId)) n := by
    rw [hco, method_old hc hs hcl]
  have hl (k : ObjId) (hk : k < h.objs.size) (n : String) :
      lookup h' (.ref k) n = lookup h (.ref k) n := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hk,
      method_old hc hs (Proof.ClsGrow.classOf_lt hc hk)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_,
      hd.nominal _ _ hr.object, classPayload_live hr.classLive, ?_⟩
    · change Boot.mainId < h'.objs.size
      dsimp only [h']
      rw [size]
      exact Nat.lt_of_lt_of_le hmain (Nat.le_add_right _ _)
    · change (h'.get Boot.mainId).payload = .none
      rw [get_old_nonclass hmain hm]; exact hr.payload
    · change ancestors h' (classOf h' (.ref Boot.mainId)) = _
      rw [hco, ancestors_old hc hs hcl]; exact hr.chain
    · change objectHookQuietB h' = true
      simpa only [objectHookQuietB, definitionHookQuietB, hl Boot.objectId hc.boot.2.2.2.2]
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
      simp only [mainConstResolve, const_own_self (name := name) (q := q) (parent := parent) (eParent := eParent) hobj,
        const_eq_own]; rfl
    · simpa only [mainConstResolve, const_own_old_other hc.boot.2.2.2.2 heq, const_from_old_other hc hs hc.boot.2.2.2.2 heq,
        const_other hc.boot.2.2.2.2 heq] using site.constants n
  · intro hf
    have hco := classOf_old (d := Boot.objectId) (name := name) (q := q) (parent := parent) (eParent := eParent) hc.boot.2.2.2.2
    have hl := Proof.ClsGrow.classOf_lt hc hc.boot.2.2.2.2
    apply (site.newDispatch hf).transport
    · rw [hco, method_old hc hs hl]
    · rw [hco, method_old hc hs hl]
    · intro owner; rw [hco, shadow_before_old hc hs hl]

#print axioms mainSite
end Ratchet.Denote.Subclass
