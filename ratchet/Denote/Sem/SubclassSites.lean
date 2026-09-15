import Denote.Sem.SubclassConstants
import Denote.Sem.SubclassDispatch
import Denote.Sem.MetaReadyClass

/-! Fresh subclass registration preserves old sites and publishes the new site's empty
table, inherited names/hook and constant scope. All superclass/metaclass ids are arbitrary. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name q : String} {parent eParent : ObjId}
local notation "h₁" => heap h Boot.objectId name q parent eParent

theorem classFront_old {k : ObjId} (hk : k < h.objs.size) : classFrontB h₁ k = classFrontB h k := by
  unfold classFrontB
  rw [grow.payloadOld (by rwa [hmid_size])]
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
    have hreg := const_own_self (name := name) (q := q) (parent := parent) (eParent := eParent) ho
    rw [instanceConstResolve, const_eq_own, hreg]
    by_cases hko : k = Boot.objectId
    · subst k
      simp only [List.firstM, hreg]; rfl
    · have hnone : constOwn h₁ k name = none := by
        rw [constOwn_old hk, constOwn_constSetIn_ne h Boot.objectId k name name _ (Or.inl hko), hold]
      simp only [List.firstM, hnone, hreg]; rfl
  · simpa only [instanceConstResolve, List.firstM, const_own_old_other hk he,
      const_own_old_other hc.boot.2.2.2.2 he, const_from_old_other hc hs hk he,
      const_other hc.boot.2.2.2.2 he] using site.constants n

theorem instanceSite_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k h) (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) : InstanceSite κ cn k h₁ := by
  have hk := site.live
  have hl : lookup h₁ (.ref k) "method_added" = lookup h (.ref k) "method_added" := by
    rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_old hk, method_old hc hs (ClsGrow.classOf_lt hc hk)]
  refine ⟨named hc.boot.2.2.2.2 hn site.named, ?_, ?_,
    instance_constants_old site hc hs ho hn, ?_, site.metaclass.subclass_old hc hs hk, ?_⟩
  · simpa only [classFront_old hk] using site.front
  · simpa only [definitionHookQuietB, hl] using site.hook
  · intro n hn owner md hm
    rw [method_old hc hs hk] at hm
    exact site.names n hn owner md hm
  · intro n hn owner md hm
    rw [classOf_old hk, method_old hc hs (ClsGrow.classOf_lt hc hk)] at hm
    exact site.classNames n hn owner md hm

theorem hook_quiet (hc : ChainsIn h) (hs : Saturated h)
    (hl : parent < h.objs.size) (he : (h.get parent).eigen = some eParent)
    (hh : definitionHookQuietB h parent = true) : definitionHookQuietB h₁ h.objs.size = true := by
  unfold definitionHookQuietB
  rw [lookup_eq_methodOn, classOf_class, method_eigen hc hs (hc.eigen parent hl eParent he)]
  simp only [definitionHookQuietB, lookup_eq_methodOn, classOf, he] at hh
  cases hm : Interp.methodOn h eParent "method_added" with
  | none => rfl
  | some pair => obtain ⟨owner, md⟩ := pair; rw [hm] at hh; exact hh

/-- Only the inherited parent capabilities are needed; no parent front/own-table shape
is assumed. This also covers Object-based creation without manufacturing an Object row. -/
theorem instanceSite {κ : Ctx} (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hl : parent < h.objs.size) (he : (h.get parent).eigen = some eParent)
    (hb : (ancestors h eParent).contains Boot.basicObjectId = true)
    (hh : definitionHookQuietB h parent = true)
    (hconst : ∀ cn, (constLookup h cn).orElse (fun _ => constLookupFrom h parent cn) = constLookup h cn)
    (hinst : NamesAt (nameFreeN κ) h parent) (hcls : NamesAt (nameFreeN κ) h eParent) :
    InstanceSite κ name h.objs.size h₁ := by
  have hel := hc.eigen parent hl eParent he
  refine ⟨named_fresh ho, ?_, hook_quiet hc hs hl he hh,
    instance_constants_fresh hc hs ho hl hconst, ?_, meta_fresh hc hs hel hb, ?_⟩
  · simp only [classFrontB, Heap.classPayload?, get_class, classObjE]; rfl
  · intro n hn owner md hm
    rw [method_class hc hs hl] at hm
    exact hinst n hn owner md hm
  · intro n hn owner md hm
    rw [classOf_class, method_eigen hc hs hel] at hm
    exact hcls n hn owner md hm

theorem scope_ready {m : Machine} {body : RubyCore.Expr}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hl : parent < m.heap.objs.size) (he : (m.heap.get parent).eigen = some eParent)
    (hh : definitionHookQuietB m.heap parent = true)
    (hcref : m.currentFrame.cref = [Boot.objectId]) (hphase : m.preludeMode = false) :
    ClassScopeReady name (machine m Boot.objectId m.currentFrame.cref name q parent eParent body) := by
  refine ⟨m.heap.objs.size, named_fresh ho, ?_, ?_, ?_, ?_, hphase, ?_, hook_quiet hc hs hl he hh⟩
  · change m.heap.objs.size < (heap m.heap Boot.objectId name q parent eParent).objs.size
    rw [size]; omega
  · rw [current_frame]; rfl
  · rw [current_frame]; simpa only [freshModFrame] using congrArg (m.heap.objs.size :: ·) hcref
  · rw [current_frame]; rfl
  · simp only [defaultDefVis, current_frame, freshModFrame]; rfl

#print axioms scope_ready
#print axioms instanceSite_old
#print axioms hook_quiet
#print axioms instanceSite
end Ratchet.Denote.Subclass
