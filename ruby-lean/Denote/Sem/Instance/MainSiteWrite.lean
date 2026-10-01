import Denote.Sem.Heap.IvarMutation

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
    simp only [Interp.methodOn, hi.ancestors_eq, hi.lookup_go_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hr := site.ready
    refine ⟨rfl, rfl, rfl, rfl, rfl, by simpa only [mainView, hi.size] using hr.live,
      by simpa only [mainView, hi.payload] using hr.payload,
      by simpa only [mainView, hi.classOf_eq, hi.ancestors_eq] using hr.chain,
      by simpa only [mainView, ha] using hr.object,
      by simpa only [mainView, hi.classPayload] using hr.classLive,
      by simpa only [mainView, objectHookQuietB, definitionHookQuietB, hi.lookup_eq] using hr.hook,
      by simpa only [mainView, hi.classPayload] using hr.detached,
      by simpa only [mainView, hi.frozen] using hr.unfrozen,
      rfl,
      by simpa only [mainView, mainOwnNamesB, ownMethods, hi.classOf_eq, hi.classPayload] using hr.mainNames,
      ?_, by simpa only [mainView, objectClassFlagsB, hi.classPayload] using hr.classFlags⟩
    change classHooksQuietB h' = true
    rw [show classHooksQuietB h' = classHooksQuietB h from
      classHooksQuietB_congr
        (by simp only [objectCallbackPrefix, hi.classOf_eq, hi.ancestors_eq])
        (fun _ _ _ => by rw [hi.classPayload])]
    exact hr.classHooks
  · intro name hn o md hl
    exact site.names name hn o md (by simpa only [hi.classOf_eq, hm] using hl)
  · intro name hb hf
    exact (hi.lookup_eq _ name).trans (site.bare name hb hf)
  · intro hf o md hl
    exact site.missing hf o md (by simpa only [hi.classOf_eq, hm] using hl)
  · intro n
    simpa only [mainConstResolve, hi.constOwn_eq, constLookupFrom, constLookup,
      hi.classPayload, hi.ancestors_eq] using site.constants n
  · intro hf
    apply (site.newDispatch hf).transport
    · simp only [hi.classOf_eq, hm]
    · intro owner
      simp only [hi.classOf_eq, hi.ancestors_eq, Interp.crubyShadow, Interp.nativeSingletonMethod, Interp.featureMethod,
        Interp.featureHas, Interp.libraryNamespace, hi.classPayload, hi.className_eq]
      rfl

#print axioms MainSite.ivarOnly
end Ratchet.Denote
