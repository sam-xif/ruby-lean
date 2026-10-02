import Denote.Sem.Class.ClassMetadataActual
import Denote.Sem.Class.ClassConstScopeActual

/-! Retain the original main-site transfer with every current readiness field. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof
variable {p : ObjId}

theorem mainSite {κ : Ctx} {m : Machine} {name : String} {e : ObjId} {h' : Heap}
    (hnames : NamesOk m.heap) (site : MainSite κ m.heap) (hc : ClassReady m.heap)
    (hs : Saturated m.heap) (htop : m.lexicalNamespace = Boot.objectId)
    (hh : h' = heap m name e p) (hdata : DataPres m.heap h') : MainSite κ h' := by
  have hch := hc.chains
  have ho := hch.boot.2.2.2.2
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ ho
  have hr := site.ready
  have hmain : Boot.mainId < m.heap.objs.size := hr.live
  have hm : m.heap.classPayload? Boot.mainId = none := by
    simp only [Heap.classPayload?, show (m.heap.get Boot.mainId).payload = .none from hr.payload]
  have hco : classOf h' (.ref Boot.mainId) = classOf m.heap (.ref Boot.mainId) := by
    rw [hh, classOf_old hd hmain]
  have hcl := ClsGrow.classOf_lt hch hmain
  have hcl' := ClsGrow.classOf_lt hch ho
  have hmo (n : String) : Interp.methodOn h' (classOf h' (.ref Boot.mainId)) n =
      Interp.methodOn m.heap (classOf m.heap (.ref Boot.mainId)) n := by
    rw [hco, hh, method_old hch hs hd hcl]
  have hl (k : ObjId) (hk : k < m.heap.objs.size) (n : String) :
      lookup h' (.ref k) n = lookup m.heap (.ref k) n := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, hh, classOf_old hd hk,
      method_old hch hs hd (ClsGrow.classOf_lt hch hk)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change MainReady (mainView h')
    refine {
      self := rfl, owner := rfl, cref := rfl, captured := rfl, phase := rfl
      live := ?_, payload := ?_, chain := ?_
      object := hdata.nominal _ _ hr.object
      classLive := ?_, hook := ?_, detached := ?_, unfrozen := ?_, origin := rfl
      mainNames := ?_, classHooks := ?_, classFlags := ?_, defFrame := rfl, singletonHooks := ?_ }
    · change Boot.mainId < h'.objs.size
      rw [hh, size m name e]
      exact Nat.lt_of_lt_of_le hmain (Nat.le_add_right _ _)
    · change (h'.get Boot.mainId).payload = .none
      rw [hh, get_old_nonclass hd hmain hm]; exact hr.payload
    · change ancestors h' (classOf h' (.ref Boot.mainId)) =
        [classOf h' (.ref Boot.mainId), Boot.objectId, Boot.kernelId, Boot.basicObjectId]
      simp only [hco]
      rw [hh, ancestors_old hch hs hd hcl]
      exact hr.chain
    · change (h'.classPayload? Boot.objectId).isSome = true
      rw [hh]
      exact (classPayload_live hd ho).trans hr.classLive
    · change objectHookQuietB h' = true
      simpa only [objectHookQuietB, definitionHookQuietB, hl Boot.objectId ho] using (show objectHookQuietB m.heap = true from hr.hook)
    · change (h'.classPayload? Boot.objectId).bind (·.attached) = none
      rw [hh, metadata_bind_old hd ho (·.attached) (fun _ => rfl)]; exact hr.detached
    · change (h'.get Boot.objectId).frozen = false
      rw [hh, (fields_old hd ho).2.2.2]; exact hr.unfrozen
    · change mainOwnNamesB h' = true
      simp only [mainOwnNamesB, ownMethods, hco]
      rw [hh, own_methods hd]
      exact hr.mainNames
    · change classHooksQuietB h' = true
      rw [hh, classHooksQuietB_eq hch hs hd]; exact hr.classHooks
    · change objectClassFlagsB h' = true
      rw [objectClassFlagsB, hh, metadata_any_old hd ho (fun cp => cp.ancestryReady && !cp.allocatorUnavailable) (fun _ => rfl)]
      exact hr.classFlags
    · change singletonHooksQuietB h' = true
      have hsites : ∀ k ∈ singletonHookSites m.heap, k < m.heap.objs.size := by
        intro k hk
        simp only [singletonHookSites, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hcl'
        · exact hch.boot.2.1
      rw [singletonHooksQuietB_congr (h := m.heap)
        (by simp only [singletonHookSites, hh, classOf_old hd ho])
        (fun k hk => by rw [hh]; exact ancestors_old hch hs hd (hsites k hk))
        (fun k hk j hj => by rw [hh]; exact own_code hd j singletonHookName)]
      exact hr.singletonHooks
  · intro n hn o md hm
    exact site.names n hn o md (by rwa [hmo] at hm)
  · intro n hb hf
    exact (hl Boot.mainId hmain n).trans (site.bare n hb hf)
  · intro hf o md hm
    exact site.missing hf o md (by rwa [hmo] at hm)
  · rw [hh]; exact main_constants hc hs htop hr.classLive site.constants
  · intro hf
    have hco : classOf h' (.ref Boot.objectId) = classOf m.heap (.ref Boot.objectId) := by
      rw [hh, classOf_old hd ho]
    have hcl := ClsGrow.classOf_lt hch ho
    apply (site.newDispatch hf).transport
    · rw [hco, hh, method_old hch hs hd hcl]
    · intro owner; rw [hco, hh, shadow_before_old hnames hch hs hd hcl]

#print axioms mainSite
end Ratchet.Denote.FreshClassActual
