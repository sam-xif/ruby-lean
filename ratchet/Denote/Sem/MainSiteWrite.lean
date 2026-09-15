import Denote.Sem.IvarMutation

/-! Field changes do not change the retained top-level dispatch world. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem MainSite.ivarOnly {κ : Ctx} {h h' : Heap} (site : MainSite κ h)
    (hi : Proof.IvarOnly h h') : MainSite κ h' := by
  have hn (cn : String) : classNamed? h' cn = classNamed? h cn := by
    simp only [classNamed?, constLookup, hi.classPayload]
  have ha (v : Value) (cn : String) : isAName h' v cn = isAName h v cn := by
    simp only [isAName, hn, isA, hi.classOf_eq, hi.ancestors_eq]
  have hm (k : ObjId) (name : String) : Interp.methodOn h' k name = Interp.methodOn h k name := by
    simp only [Interp.methodOn, hi.classPayload, hi.ancestors_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hr := site.ready
    exact ⟨rfl, rfl, rfl, rfl, rfl, by simpa only [mainView, hi.size] using hr.live,
      by simpa only [mainView, hi.payload] using hr.payload,
      by simpa only [mainView, hi.classOf_eq, hi.ancestors_eq] using hr.chain,
      by simpa only [mainView, ha] using hr.object,
      by simpa only [mainView, hi.classPayload] using hr.classLive,
      by simpa only [mainView, objectHookQuietB, definitionHookQuietB, hi.lookup_eq] using hr.hook⟩
  · intro name hn o md hl
    exact site.names name hn o md (by simpa only [hi.classOf_eq, hm] using hl)
  · intro name hb hf
    exact (hi.lookup_eq _ name).trans (site.bare name hb hf)
  · intro hf o md hl
    exact site.missing hf o md (by simpa only [hi.classOf_eq, hm] using hl)
  · intro n
    simpa only [mainConstResolve, hi.constOwn_eq, constLookupFrom, constLookup,
      hi.classPayload, hi.ancestors_eq] using site.constants n

#print axioms MainSite.ivarOnly
end Ratchet.Denote
