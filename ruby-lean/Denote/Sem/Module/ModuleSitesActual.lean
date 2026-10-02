import Denote.Sem.Module.ModuleInstanceConstantsActual
import Denote.Sem.Module.ModuleBase
import Denote.Sem.Class.ClassSitesActual

/-! Site publication/transport through actual module registration. -/

set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String} 
local notation "h₁" => heap m name

theorem moduleBase {κ : Ctx} (hp : ModuleBase κ m.heap)
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) : ModuleBase κ h₁ :=
  hp.transport (method_old hc hs (htop ▸ hc.boot.2.2.2.2) hc.boot.2.1)
    (fallback_old hc hs htop ho hc.boot.2.1 hp.constants)

theorem classFront_old {k : ObjId} (hd : m.lexicalNamespace < m.heap.objs.size)
    (hk : k < m.heap.objs.size) : classFrontB h₁ k = classFrontB m.heap k :=
  metadata_any_old hd hk (fun cp => cp.prepends.isEmpty) (fun _ => rfl)

theorem meta_old {k : ObjId} (hp : MetaReady m.heap k)
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) : MetaReady h₁ k :=
  hp.transport (fields_old hd hk).2.2.1
    (fun j hj => ancestors_old hc hs hd (hc.eigen k hk j hj))

theorem instanceSite_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k m.heap) (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hmain : ∀ n, constLookupFrom m.heap Boot.objectId n = constLookup m.heap n)
    (hreach : Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true) :
    InstanceSite κ cn k h₁ := by
  have hk := site.live
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  have hkl := ClsGrow.classOf_lt hc.chains hk
  have hl : lookup h₁ (.ref k) "method_added" = lookup m.heap (.ref k) "method_added" := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hd hk, method_old hc.chains hs hd hkl]
  have hls : lookup h₁ (.ref k) singletonHookName = lookup m.heap (.ref k) singletonHookName := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hd hk, method_old hc.chains hs hd hkl]
  have hli : lookup h₁ (.ref k) "inherited" = lookup m.heap (.ref k) "inherited" := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hd hk, method_old hc.chains hs hd hkl]
  refine ⟨named_old htop hc.chains.boot.2.2.2.2 hn site.named, ?_, ?_,
    instance_constants_old site hc hs htop ho hn hmain hreach, ?_,
    meta_old site.metaclass hc.chains hs hd hk, ?_, ?_, ?_, ?_, site.afterBuiltins,
    by rw [metadata_bind_old hd hk (·.attached) (fun _ => rfl)]; exact site.detached,
    (fields_old hd hk).2.2.2.trans site.unfrozen,
    by rw [size]; exact Nat.lt_of_lt_of_le site.mainLive (Nat.le_add_right _ _),
    by rw [classOf_old hd site.mainLive]; exact site.notMain,
    by obtain ⟨e', hke, ha, hf⟩ := site.metaAttached
       have hel : e' < m.heap.objs.size := hc.chains.eigen k hk e' hke
       exact ⟨e', by rw [(fields_old hd hk).2.2.1]; exact hke,
         by rw [metadata_bind_old hd hel (·.attached) (fun _ => rfl)]; exact ha,
         by rw [(fields_old hd hel).2.2.2]; exact hf⟩,
    by simpa only [singletonDefHookQuietB, hls] using site.singletonHook,
    by rw [classOf_old hd hk, classOf_old hd site.mainLive]; exact site.metaNotMain,
    by simpa only [inheritedHookQuietB, hli, metadata_any_old hd hk (·.isModule) (fun _ => rfl)]
      using site.inheritedHook⟩
  · simpa only [classFront_old hd hk] using site.front
  · simpa only [definitionHookQuietB, hl] using site.hook
  · intro n hn owner md hm
    rw [method_old hc.chains hs hd hk] at hm
    exact site.names n hn owner md hm
  · intro n hn owner md hm
    rw [classOf_old hd hk, method_old hc.chains hs hd hkl] at hm
    exact site.classNames n hn owner md hm
  · simpa only [classOf_old hd hk, classFront_old hd hkl] using site.metaFront
  · simpa only [classOf_old hd hk, (fields_old hd hkl).2.2.1] using site.metaLeaf
  · rw [classOf_old hd hk]
    exact fallback_old hc.chains hs htop ho hkl site.metaConstants

theorem meta_fresh (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size)
    (hb : (ancestors m.heap Boot.moduleId).contains Boot.basicObjectId = true) :
    MetaReady h₁ m.heap.objs.size := by
  refine ⟨m.heap.objs.size + 1, ?_, ?_, ?_⟩
  · rw [get_module hd]
  · rw [ancestors_eigen hc.chains hs hd]
    simp only [List.contains_cons, hb, Bool.or_true]
  · intro base ch hbase
    exact (Nat.ne_of_lt (Nat.lt_succ_of_lt
      (Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.chains.boot.2.2.2.1))).symm

theorem instanceSite {κ : Ctx} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hbase : ModuleBase κ m.heap)
    (hb : (ancestors m.heap Boot.moduleId).contains Boot.basicObjectId = true)
    (hmain : ∀ n, constLookupFrom m.heap Boot.objectId n = constLookup m.heap n)
    (hboot : Boot.yielderId < m.heap.objs.size) (hml : Boot.mainId < m.heap.objs.size)
    (hsq : singletonHooksQuietB m.heap = true) :
    InstanceSite κ name m.heap.objs.size h₁ := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  refine ⟨named_fresh htop ho, ?_, hook_quiet hc.chains hs hd hbase.hook,
    instance_constants_fresh hc hs htop ho hmain, ?_, meta_fresh hc hs hd hb, ?_, ?_, ?_, ?_, hboot,
    ?_, ?_, by rw [size]; exact Nat.lt_of_lt_of_le hml (Nat.le_add_right _ _),
    by rw [classOf_old hd hml]; exact (Nat.ne_of_lt (ClsGrow.classOf_lt hc.chains hml)).symm,
    ⟨m.heap.objs.size + 1, by rw [get_module hd],
      by simp only [Heap.classPayload?, get_eigen, attachedModuleEigen]; rfl,
      by rw [get_eigen]; rfl⟩,
    singletonDefHookQuietB_of_methodOn (classOf_module hd)
      (by rw [method_eigen hc.chains hs hd]
          exact singletonHooksQuietB_methodOn hsq hc.chains (by simp [singletonHookSites])),
    by rw [classOf_module hd, classOf_old hd hml]
       exact (Nat.ne_of_lt (Nat.lt_succ_of_lt (ClsGrow.classOf_lt hc.chains hml))).symm,
    by simp [inheritedHookQuietB, Heap.classPayload?, get_module hd, namedObject, modPayload]⟩
  · simp only [classFrontB, Heap.classPayload?, get_module hd, namedObject, modPayload]; rfl
  · intro n hn owner md hm
    rw [method_module hc.chains hd] at hm
    cases hm
  · intro n hn owner md hm
    rw [classOf_module hd, method_eigen hc.chains hs hd] at hm
    exact hbase.names n hn owner md hm
  · simp only [classOf_module hd, classFrontB, Heap.classPayload?, get_eigen, attachedModuleEigen]; rfl
  · simp only [classOf_module hd, get_eigen, attachedModuleEigen]
  · rw [classOf_module hd]
    exact fallback_fresh_meta hc.chains hs htop ho hbase.constants
  · change ((heap m name).classPayload? m.heap.objs.size).bind (·.attached) = none
    simp only [Heap.classPayload?, get_module hd, namedObject, modPayload]; rfl
  · change ((heap m name).get m.heap.objs.size).frozen = false
    rw [get_module hd]; rfl

#print axioms moduleBase
#print axioms instanceSite_old
#print axioms instanceSite
end Ratchet.Denote.FreshModuleActual
