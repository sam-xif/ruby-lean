import Denote.Sem.InstanceSite
import Denote.Sem.ClassConstants
import Denote.Sem.ClassCore
import Denote.Sem.MetaReadyClass

/-! A fresh top-level class preserves existing instance-call sites. The newly bound
constant is handled separately: absence is not stable, but lexical/global agreement is. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem classFront_old (ho : Boot.objectId < h.objs.size) {k : ObjId}
    (hk : k < h.objs.size) : classFrontB h₁ k = classFrontB h k := by
  unfold classFrontB
  rw [Proof.Judgment.freshClsHeap_cp_old ho hk]
  have hh := congrArg (fun s => s.any (fun shape => shape.1.isEmpty))
    (Proof.shape_constSetIn h Boot.objectId k name (.ref h.objs.size))
  simpa only [Option.any_map, Function.comp_def, Proof.clsShape] using hh

theorem instance_constants_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k h) (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) :
    ∀ n, instanceConstResolve h₁ k n = constLookup h₁ n := by
  have hk := named_live site.named
  intro n
  by_cases he : n = name
  · subst n
    have hold : constOwn h k name = none := by
      have hcst := site.constants name
      rw [instanceConstResolve, constLookup_eq_own, hn] at hcst
      cases hv : constOwn h k name with
      | none => rfl
      | some v => simp only [List.firstM, hv] at hcst; cases hcst
    have hreg := const_self (name := name) (e := e) ho
    rw [instanceConstResolve, constLookup_eq_own, hreg]
    by_cases hko : k = Boot.objectId
    · subst k
      simp only [List.firstM, hreg]; rfl
    · have hnone : constOwn h₁ k name = none := by
        rw [Proof.Judgment.constOwn_old_freshC hc.boot.2.2.2.2 hk,
          Proof.constOwn_constSetIn_ne h Boot.objectId k name name _ (Or.inl hko), hold]
      simp only [List.firstM, hnone, hreg]; rfl
  · simpa only [instanceConstResolve, List.firstM,
      const_own_old_other hc.boot.2.2.2.2 hk he,
      const_own_old_other hc.boot.2.2.2.2 hc.boot.2.2.2.2 he,
      const_from_old_other hc hs hk he, const_other hc.boot.2.2.2.2 he] using site.constants n

theorem instanceSite_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k h) (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) : InstanceSite κ cn k h₁ := by
  have hk := named_live site.named
  have hl : lookup h₁ (.ref k) "method_added" = lookup h (.ref k) "method_added" := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hk,
      method_old hc hs (Proof.ClsGrow.classOf_lt hc hk)]
  refine ⟨named hc.boot.2.2.2.2 hn site.named, ?_, ?_,
    instance_constants_old site hc hs ho hn, ?_, site.metaclass.subclass_old hc hs hk, ?_⟩
  · simpa only [classFront_old hc.boot.2.2.2.2 hk] using site.front
  · simpa only [definitionHookQuietB, hl] using site.hook
  · intro n hn owner md hm
    rw [method_old hc hs hk] at hm
    exact site.names n hn owner md hm
  · intro n hn owner md hm
    rw [classOf_old hk, method_old hc hs (Proof.ClsGrow.classOf_lt hc hk)] at hm
    exact site.classNames n hn owner md hm

#print axioms instance_constants_old
#print axioms instanceSite_old
end Ratchet.Denote.FreshClass
