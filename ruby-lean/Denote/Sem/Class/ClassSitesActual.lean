import Denote.Sem.Class.ClassInstanceConstantsActual
import Denote.Sem.Module.ModuleBase

/-! Reuse the original site publication/transport, with the repaired constant premise. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e

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
  refine ⟨named_old htop hc.chains.boot.2.2.2.2 hn site.named, ?_, ?_,
    instance_constants_old site hc hs htop ho hn hmain hreach, ?_,
    meta_old site.metaclass hc.chains hs hd hk, ?_, ?_, ?_, ?_, site.afterBuiltins⟩
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
    (he : (m.heap.get Boot.objectId).eigen = some e) : MetaReady h₁ m.heap.objs.size := by
  obtain ⟨j, hj, hb, _⟩ := hc.metaObject
  rw [he] at hj; cases hj
  have hel := hc.chains.eigen _ hc.chains.boot.2.2.2.2 _ he
  refine ⟨m.heap.objs.size + 1, ?_, ?_, ?_⟩
  · rw [get_class hd]
  · rw [ancestors_eigen hc.chains hs hd hel]
    simp only [List.contains_cons, hb, Bool.or_true]
  · intro base ch hbase
    exact (Nat.ne_of_lt (Nat.lt_succ_of_lt
      (Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.chains.boot.2.2.2.1))).symm

theorem instanceSite {κ : Ctx} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hh : definitionHookQuietB m.heap Boot.objectId = true)
    (hmain : ∀ n, constLookupFrom m.heap Boot.objectId n = constLookup m.heap n)
    (hinst : NamesAt (nameFreeN κ) m.heap Boot.objectId)
    (hcls : NamesAt (nameFreeN κ) m.heap e)
    (hmeta : ConstFallback m.heap e) (hboot : Boot.yielderId < m.heap.objs.size) :
    InstanceSite κ name m.heap.objs.size h₁ := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  have hel := hc.chains.eigen _ hc.chains.boot.2.2.2.2 _ he
  refine ⟨named_fresh htop ho, ?_, hook_quiet hc.chains hs hd he hh,
    instance_constants_fresh hc hs htop ho hmain, ?_, meta_fresh hc hs hd he, ?_, ?_, ?_, ?_, hboot⟩
  · simp only [classFrontB, Heap.classPayload?, get_class hd, namedObject, freshClassPayload]; rfl
  · intro n hn owner md hm
    rw [method_class hc.chains hs hd] at hm
    exact hinst n hn owner md hm
  · intro n hn owner md hm
    rw [classOf_class hd, method_eigen hc.chains hs hd hel] at hm
    exact hcls n hn owner md hm
  · simp only [classOf_class hd, classFrontB, Heap.classPayload?, get_eigen, attachedClassEigen]; rfl
  · simp only [classOf_class hd, get_eigen, attachedClassEigen]
  · rw [classOf_class hd]
    exact fallback_fresh_meta hc.chains hs htop ho hel hmeta

#print axioms moduleBase
#print axioms instanceSite_old
#print axioms instanceSite
end Ratchet.Denote.FreshClassActual
