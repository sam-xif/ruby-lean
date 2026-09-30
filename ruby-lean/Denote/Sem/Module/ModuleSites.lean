import Denote.Sem.Module.ModuleConstants
import Denote.Sem.Module.ModuleDispatch

/-! Module creation preserves old sites and publishes its empty own table plus the
singleton capabilities retained at Module. No ordinary-class ancestry is assumed. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem moduleBase {κ : Ctx} (hp : ModuleBase κ h) (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true) : ModuleBase κ h₁ :=
  hp.transport (method_old hc hs hc.boot.2.1) (fallback_old hc hs ho hc.boot.2.1 hp.constants)

theorem classFront_old {k : ObjId} (hk : k < h.objs.size) : classFrontB h₁ k = classFrontB h k := by
  unfold classFrontB
  rw [clsGrow_hmid_fresh.payloadOld (by rwa [hmid_size])]
  have hh := congrArg (fun s => s.any (fun shape => shape.1.isEmpty))
    (shape_constSetIn h Boot.objectId k name (.ref h.objs.size))
  simpa only [Option.any_map, Function.comp_def, clsShape] using hh

theorem instance_constants_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k h) (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) :
    ∀ n, instanceConstResolve h₁ k n = constLookup h₁ n := by
  have hk := site.live
  intro n
  by_cases he : n = name
  · subst n
    have hold : constOwn h k name = none := by
      have hcst := site.constants name
      rw [instanceConstResolve, const_eq_own, hn] at hcst
      cases hv : constOwn h k name with
      | none => rfl
      | some v => simp only [List.firstM, hv] at hcst; cases hcst
    have hreg := const_self (name := name) ho
    rw [const_eq_own] at hreg
    rw [instanceConstResolve, const_eq_own, hreg]
    by_cases hko : k = Boot.objectId
    · subst k
      simp only [List.firstM, hreg]; rfl
    · have hnone : constOwn h₁ k name = none := by
        rw [constOwn_old_fresh hc.boot.2.2.2.2 hk, constOwn_constSetIn_ne h Boot.objectId k name name _ (Or.inl hko), hold]
      simp only [List.firstM, hnone, hreg]; rfl
  · simpa only [instanceConstResolve, List.firstM, const_own_old_other hc.boot.2.2.2.2 hk he,
      const_own_old_other hc.boot.2.2.2.2 hc.boot.2.2.2.2 he, const_from_old_other hc hs hk he,
      const_other hc.boot.2.2.2.2 he] using site.constants n

theorem instanceSite_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k h) (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) : InstanceSite κ cn k h₁ := by
  have hk := site.live
  have hl : lookup h₁ (.ref k) "method_added" = lookup h (.ref k) "method_added" := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hk, method_old hc hs (ClsGrow.classOf_lt hc hk)]
  refine ⟨named hc.boot.2.2.2.2 hn site.named, ?_, ?_,
    instance_constants_old site hc hs ho hn, ?_, meta_old site.metaclass hc hs hk, ?_, ?_, ?_, ?_⟩
  · simpa only [classFront_old hk] using site.front
  · simpa only [definitionHookQuietB, hl] using site.hook
  · intro n hn owner md hm
    rw [method_old hc hs hk] at hm
    exact site.names n hn owner md hm
  · intro n hn owner md hm
    rw [classOf_old hk, method_old hc hs (ClsGrow.classOf_lt hc hk)] at hm
    exact site.classNames n hn owner md hm
  · simpa only [classOf_old hk, classFront_old (ClsGrow.classOf_lt hc hk)] using site.metaFront
  · simpa only [classOf_old hk, (fields (ClsGrow.classOf_lt hc hk)).2.2.1] using site.metaLeaf
  · rw [classOf_old hk]
    exact fallback_old hc hs ho (ClsGrow.classOf_lt hc hk) site.metaConstants

theorem hook_quiet {κ : Ctx} (hp : ModuleBase κ h) (hc : ChainsIn h) (hs : Saturated h) :
    definitionHookQuietB h₁ h.objs.size = true := by
  unfold definitionHookQuietB
  rw [lookup_eq_methodOn, classOf_fresh_k, method_eigen hc hs]
  have hh := hp.hook
  unfold moduleHookQuietB at hh
  exact hh

theorem instanceSite {κ : Ctx} (hp : ModuleBase κ h) (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hb : (ancestors h Boot.moduleId).contains Boot.basicObjectId = true) :
    InstanceSite κ name h.objs.size h₁ := by
  refine ⟨named_new hc.boot.2.2.2.2 ho, ?_, hook_quiet hp hc hs,
    instance_constants_fresh, ?_, meta_fresh hc hs hb, ?_, ?_, ?_, ?_⟩
  · simp only [classFrontB, freshModHeap_cp_k]; rfl
  · intro n _ owner md hm
    rw [method_fresh] at hm; cases hm
  · intro n hn owner md hm
    rw [classOf_fresh_k, method_eigen hc hs] at hm
    exact hp.names n hn owner md hm
  · simp only [classOf_fresh_k, classFrontB, freshModHeap_cp_e]; rfl
  · simp only [classOf_fresh_k, freshModHeap_get_e, eigObj]
  · rw [classOf_fresh_k]
    exact fallback_fresh_meta hc hs ho hp.constants

theorem scope_ready {κ : Ctx} {m : Machine} {body : RubyCore.Expr}
    (hp : ModuleBase κ m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hcref : m.currentFrame.cref = [Boot.objectId]) (hphase : m.preludeMode = false) :
    ClassScopeReady name (freshModMachine m Boot.objectId m.currentFrame.cref name name body) := by
  refine ⟨m.heap.objs.size, named_new hc.boot.2.2.2.2 ho, ?_, ?_, ?_, ?_, hphase, ?_,
    hook_quiet hp hc hs⟩
  · change m.heap.objs.size < (freshModHeap m.heap Boot.objectId name name).objs.size
    rw [freshModHeap_size]; omega
  · rw [current_frame]; rfl
  · rw [current_frame]; simpa only [freshModFrame] using congrArg (m.heap.objs.size :: ·) hcref
  · rw [current_frame]; rfl
  · simp only [defaultDefVis, current_frame, freshModFrame]; rfl

#print axioms moduleBase
#print axioms instanceSite_old
#print axioms instanceSite
#print axioms scope_ready
end Ratchet.Denote.FreshModule
