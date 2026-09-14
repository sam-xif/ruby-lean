import Denote.Sem.InstanceSite
import Denote.Sem.MethodHeap
import Ratchet.MethodCtx

/-! Preserve a class's instance-call site while installing methods or writing fields.
Reserving a name weakens absence facts; it does not install or certify a callable body. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem InstanceSite.recontext {κ κ' : Ctx} {cn : String} {k : ObjId} {h : Heap}
    (site : InstanceSite κ cn k h)
    (hn : ∀ n, nameFreeN κ n = false → nameFreeN κ' n = false) : InstanceSite κ' cn k h := by
  refine ⟨site.named, site.front, site.hook, site.constants, ?_⟩
  intro n hmem owner md hm
  rcases site.names n hmem owner md hm with hb | hu | hf
  · exact Or.inl hb
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (hn n hf))

theorem InstanceSite.reserveName {κ : Ctx} {cn : String} {k : ObjId} {h : Heap}
    (site : InstanceSite κ cn k h) (name : String) :
    InstanceSite (reserveNameCtx κ name) cn k h := by
  apply site.recontext
  intro n hn
  cases hu : κ.negUnpinned <;>
    simp_all [nameFreeN, reserveNameCtx, Ctx.declared, Ctx.negUnpinned]

theorem classFrontB_defineMethod (h : Heap) (cls k : ObjId) (name : String) (md : MethodDef) :
    classFrontB (defineMethod h cls name md) k = classFrontB h k := by
  have hh := congrArg (fun s => s.any (fun shape => shape.1.isEmpty))
    (Proof.shape_defineMethod h cls k name md)
  simpa only [Option.any_map, Function.comp_def, Proof.clsShape, classFrontB] using hh

/-- The written name must be reserved, and a new method_added needs a different hook
proof. The owner is arbitrary: aliases and writes to other classes are covered too. -/
theorem InstanceSite.methodWrite {κ : Ctx} {cn name : String} {k cls : ObjId}
    {h : Heap} {md : MethodDef} (site : InstanceSite κ cn k h)
    (hn : nameFreeN κ name = false) (hq : "method_added" ≠ name) :
    InstanceSite κ cn k (defineMethod h cls name md) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [classNamed?_defineMethod] using site.named
  · simpa only [classFrontB_defineMethod] using site.front
  · simpa only [definitionHookQuietB,
      Proof.lookup_defineMethod h cls name "method_added" md (.ref k) hq
        (Proof.classOf_defineMethod ..)] using site.hook
  · intro n
    simpa only [instanceConstResolve, Proof.constOwn_defineMethod,
      Proof.constLookupFrom_defineMethod, constLookup_defineMethod] using site.constants n
  · intro n hmem owner found hfound
    by_cases he : n = name
    · exact Or.inr (Or.inr (he ▸ hn))
    · rw [methodOn_defineMethod _ _ _ _ _ _ he] at hfound
      exact site.names n hmem owner found hfound

theorem InstanceSite.ivarOnly {κ : Ctx} {cn : String} {k : ObjId} {h h' : Heap}
    (site : InstanceSite κ cn k h) (hi : Proof.IvarOnly h h') : InstanceSite κ cn k h' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [classNamed?, constLookup, hi.classPayload] using site.named
  · simpa only [classFrontB, hi.classPayload] using site.front
  · simpa only [definitionHookQuietB, hi.lookup_eq] using site.hook
  · intro n
    simpa only [instanceConstResolve, hi.constOwn_eq, constLookupFrom,
      hi.classPayload, hi.ancestors_eq, constLookup] using site.constants n
  · intro n hmem owner md hm
    simp only [Interp.methodOn, hi.classPayload, hi.ancestors_eq] at hm
    exact site.names n hmem owner md hm

#print axioms InstanceSite.methodWrite
#print axioms InstanceSite.ivarOnly
end Ratchet.Denote
