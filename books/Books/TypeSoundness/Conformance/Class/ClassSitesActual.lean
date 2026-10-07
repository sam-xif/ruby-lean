import Books.TypeSoundness.Conformance.Class.ClassInstanceConstantsActual
import Books.TypeSoundness.Conformance.Module.ModuleBase

/-! Reuse the original site publication/transport, with the repaired constant premise. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {p : ObjId}
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e p

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
  refine ⟨named_old (p := p) htop hc.chains.boot.2.2.2.2 hn site.named, ?_, ?_,
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
      using site.inheritedHook,
    by simpa only [Interp.libraryNamespace, metadata_bind_old hd hk (·.libraryNamespace) (fun _ => rfl)]
      using site.library⟩
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
    (hd : m.lexicalNamespace < m.heap.objs.size) (hpl : p < m.heap.objs.size)
    (hmr : MetaReady m.heap p) (he : (m.heap.get p).eigen = some e) :
    MetaReady h₁ m.heap.objs.size := by
  obtain ⟨j, hj, hb, _⟩ := hmr
  rw [he] at hj; cases hj
  have hel := hc.chains.eigen _ hpl _ he
  refine ⟨m.heap.objs.size + 1, ?_, ?_, ?_⟩
  · rw [get_class hd]
  · rw [ancestors_eigen hc.chains hs hd hel]
    simp only [List.contains_cons, hb, Bool.or_true]
  · intro base ch hbase
    exact (Nat.ne_of_lt (Nat.lt_succ_of_lt
      (Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.chains.boot.2.2.2.1))).symm

/-- The fresh class's site, from its parent's site facts (Object or a declared class). -/
theorem instanceSiteAt {κ : Ctx} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) (hpl : p < m.heap.objs.size)
    (hmr : MetaReady m.heap p) (he : (m.heap.get p).eigen = some e)
    (hh : definitionHookQuietB m.heap p = true)
    (hpc : ∀ n, constLookupFrom h₁ p n = constLookup h₁ n)
    (hinst : NamesAt (nameFreeN κ) m.heap p)
    (hcls : NamesAt (nameFreeN κ) m.heap e)
    (hmeta : ConstFallback m.heap e) (hboot : Boot.yielderId < m.heap.objs.size)
    (hml : Boot.mainId < m.heap.objs.size) (hsh : singletonDefHookQuietB m.heap p = true)
    (hih : (lookup m.heap (.ref p) "inherited").any (fun (_, md) =>
      !md.undefined && md.builtin == some "Class#inherited") = true) :
    InstanceSite κ name m.heap.objs.size h₁ := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  have hel := hc.chains.eigen _ hpl _ he
  refine ⟨named_fresh htop ho, ?_, hook_quiet hc.chains hs hd hpl he hh,
    instance_constants_parent hc hs htop hpl hpc, ?_, meta_fresh hc hs hd hpl hmr he, ?_, ?_, ?_, ?_, hboot,
    ?_, ?_, by rw [size]; exact Nat.lt_of_lt_of_le hml (Nat.le_add_right _ _),
    by rw [classOf_old hd hml]; exact (Nat.ne_of_lt (ClsGrow.classOf_lt hc.chains hml)).symm,
    ⟨m.heap.objs.size + 1, by rw [get_class hd],
      by simp only [Heap.classPayload?, get_eigen, attachedClassEigen]; rfl,
      by rw [get_eigen]; rfl⟩,
    by unfold singletonDefHookQuietB
       rw [lookup_eq_methodOn, classOf_class hd, method_eigen hc.chains hs hd hel]
       simp only [singletonDefHookQuietB, lookup_eq_methodOn, classOf, he] at hsh
       exact hsh,
    by rw [classOf_class hd, classOf_old hd hml]
       exact (Nat.ne_of_lt (Nat.lt_succ_of_lt (ClsGrow.classOf_lt hc.chains hml))).symm,
    by unfold inheritedHookQuietB
       rw [lookup_eq_methodOn, classOf_class hd, method_eigen hc.chains hs hd hel]
       simp only [lookup_eq_methodOn, classOf, he] at hih
       simp only [hih, Bool.or_true],
    by simp [Interp.libraryNamespace, Heap.classPayload?, get_class hd, namedObject, freshClassPayload]⟩
  · simp only [classFrontB, Heap.classPayload?, get_class hd, namedObject, freshClassPayload]; rfl
  · intro n hn owner md hm
    rw [method_class hc.chains hs hd hpl] at hm
    exact hinst n hn owner md hm
  · intro n hn owner md hm
    rw [classOf_class hd, method_eigen hc.chains hs hd hel] at hm
    exact hcls n hn owner md hm
  · simp only [classOf_class hd, classFrontB, Heap.classPayload?, get_eigen, attachedClassEigen]; rfl
  · simp only [classOf_class hd, get_eigen, attachedClassEigen]
  · rw [classOf_class hd]
    exact fallback_fresh_meta hc.chains hs htop ho hel hmeta
  · change ((heap m name e p).classPayload? m.heap.objs.size).bind (·.attached) = none
    simp only [Heap.classPayload?, get_class hd, namedObject, freshClassPayload]; rfl
  · change ((heap m name e p).get m.heap.objs.size).frozen = false
    rw [get_class hd]; rfl

theorem instanceSite {κ : Ctx} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hh : definitionHookQuietB m.heap Boot.objectId = true)
    (hmain : ∀ n, constLookupFrom m.heap Boot.objectId n = constLookup m.heap n)
    (hinst : NamesAt (nameFreeN κ) m.heap Boot.objectId)
    (hcls : NamesAt (nameFreeN κ) m.heap e)
    (hmeta : ConstFallback m.heap e) (hboot : Boot.yielderId < m.heap.objs.size)
    (hml : Boot.mainId < m.heap.objs.size) (hsq : singletonHooksQuietB m.heap = true)
    (hcq : classHooksQuietB m.heap = true) :
    InstanceSite κ name m.heap.objs.size (heap m name e Boot.objectId) :=
  instanceSiteAt hc hs htop ho hc.chains.boot.2.2.2.2 hc.metaObject he hh
    (main_constants hc hs htop ho hmain) hinst hcls hmeta hboot hml
    (singletonDefHookQuietB_of_methodOn (by simp only [classOf, he]; rfl)
      (by have hco : e = classOf m.heap (.ref Boot.objectId) := by simp only [classOf, he]
          rw [hco]
          exact singletonHooksQuietB_methodOn hsq hc.chains (by simp [singletonHookSites])))
    (by obtain ⟨owner, md, hl, hu, hb⟩ := classHooksQuietB_lookup hcq hc.chains
          (by simp [classHookNames] : ("inherited", "Class#inherited") ∈ classHookNames)
        simp [hl, hu, hb])

#print axioms moduleBase
#print axioms instanceSite_old
#print axioms instanceSite
end Checker.Soundness.FreshClassActual
