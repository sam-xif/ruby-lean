import Denote.Sem.Instance.InstanceSite
import Denote.Sem.Instance.MethodHeap
import Ratchet.Guards.MethodCtx
import Ratchet.Guards.ClassCtx

/-! Preserve a class's instance-call site while installing methods or writing fields.
Reserving a name weakens absence facts; it does not install or certify a callable body. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

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
    (hn : nameFreeN κ name = false) (hq : "method_added" ≠ name)
    (hsh : singletonHookName ≠ name) :
    InstanceSite κ cn k (defineMethod h cls name md) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, site.metaclass.methodWrite, ?_, ?_, ?_, ?_, site.afterBuiltins,
    by rw [attached_defineMethod]; exact site.detached,
    (congrArg Object.frozen (get_defineMethod_data h cls k name md)).trans site.unfrozen,
    by simpa only [Proof.objs_size_defineMethod] using site.mainLive,
    by simpa only [Proof.classOf_defineMethod] using site.notMain,
    by obtain ⟨e, hke, ha, hf⟩ := site.metaAttached
       exact ⟨e, by rw [Proof.get_defineMethod_eigen]; exact hke, by rw [attached_defineMethod]; exact ha,
         (congrArg Object.frozen (get_defineMethod_data h cls e name md)).trans hf⟩,
    by simpa only [singletonDefHookQuietB,
      Proof.lookup_defineMethod h cls name singletonHookName md (.ref k) hsh
        (Proof.classOf_defineMethod ..)] using site.singletonHook,
    by simpa only [Proof.classOf_defineMethod] using site.metaNotMain⟩
  · simpa only [classNamed?_defineMethod] using site.named
  · simpa only [classFrontB_defineMethod] using site.front
  · simpa only [definitionHookQuietB,
      Proof.lookup_defineMethod h cls name "method_added" md (.ref k) hq
        (Proof.classOf_defineMethod ..)] using site.hook
  · intro n
    simpa only [instanceConstResolve, Proof.constOwn_defineMethod,
      Proof.constLookupFrom_defineMethod, constLookup_defineMethod, isModuleAny_defineMethod] using site.constants n
  · intro n hmem owner found hfound
    by_cases he : n = name
    · exact Or.inr (Or.inr (he ▸ hn))
    · rw [methodOn_defineMethod _ _ _ _ _ _ he] at hfound
      exact site.names n hmem owner found hfound
  · intro n hmem owner found hfound
    by_cases he : n = name
    · exact Or.inr (Or.inr (he ▸ hn))
    · rw [Proof.classOf_defineMethod, methodOn_defineMethod _ _ _ _ _ _ he] at hfound
      exact site.classNames n hmem owner found hfound
  · simpa only [Proof.classOf_defineMethod, classFrontB_defineMethod] using site.metaFront
  · simpa only [Proof.classOf_defineMethod, Proof.get_defineMethod_eigen] using site.metaLeaf
  · simpa only [Proof.classOf_defineMethod] using site.metaConstants.methodWrite

theorem InstanceSite.ivarOnly {κ : Ctx} {cn : String} {k : ObjId} {h h' : Heap}
    (site : InstanceSite κ cn k h) (hi : Proof.IvarOnly h h') : InstanceSite κ cn k h' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, site.metaclass.ivarOnly hi, ?_, ?_, ?_, ?_, site.afterBuiltins,
    by simpa only [hi.classPayload] using site.detached,
    by simpa only [hi.frozen] using site.unfrozen,
    by simpa only [hi.size] using site.mainLive,
    by simpa only [hi.classOf_eq] using site.notMain,
    by obtain ⟨e, hke, ha, hf⟩ := site.metaAttached
       exact ⟨e, by rw [hi.eigen]; exact hke, by rw [hi.classPayload]; exact ha, by rw [hi.frozen]; exact hf⟩,
    by simpa only [singletonDefHookQuietB, hi.lookup_eq] using site.singletonHook,
    by simpa only [hi.classOf_eq] using site.metaNotMain⟩
  · simpa only [classNamed?, constLookup, hi.classPayload] using site.named
  · simpa only [classFrontB, hi.classPayload] using site.front
  · simpa only [definitionHookQuietB, hi.lookup_eq] using site.hook
  · intro n
    simpa only [instanceConstResolve, hi.constOwn_eq, constLookupFrom,
      hi.classPayload, hi.ancestors_eq, constLookup] using site.constants n
  · intro n hmem owner md hm
    simp only [Interp.methodOn, hi.ancestors_eq, hi.lookup_go_eq] at hm
    exact site.names n hmem owner md hm
  · intro n hmem owner md hm
    simp only [hi.classOf_eq, Interp.methodOn, hi.ancestors_eq, hi.lookup_go_eq] at hm
    exact site.classNames n hmem owner md hm
  · simpa only [hi.classOf_eq, classFrontB, hi.classPayload] using site.metaFront
  · simpa only [hi.classOf_eq, hi.eigen] using site.metaLeaf
  · simpa only [hi.classOf_eq] using site.metaConstants.ivarOnly hi

theorem ClassSitesOk.methodWrite {κ : Ctx} {name : String} {cls : ObjId}
    {h : Heap} {md : MethodDef} (sites : ClassSitesOk κ h)
    (hn : nameFreeN κ name = false) (hq : "method_added" ≠ name)
    (hsh : singletonHookName ≠ name) :
    ClassSitesOk κ (defineMethod h cls name md) := by
  intro cn hcn
  obtain ⟨k, site⟩ := sites cn hcn
  exact ⟨k, site.methodWrite hn hq hsh⟩

theorem ClassSitesOk.ivarOnly {κ : Ctx} {h h' : Heap} (sites : ClassSitesOk κ h)
    (hi : Proof.IvarOnly h h') : ClassSitesOk κ h' := by
  intro cn hcn
  obtain ⟨k, site⟩ := sites cn hcn
  exact ⟨k, site.ivarOnly hi⟩

theorem ClassSitesOk.publish_instance {κ : Ctx} {c : Cls} {d : Defn} {cls : ObjId}
    {h : Heap} {md : MethodDef} (sites : ClassSitesOk κ h)
    (site : InstanceSite κ c.name cls h) (hq : "method_added" ≠ d.name)
    (hsh : singletonHookName ≠ d.name) :
    ClassSitesOk (instanceDeclCtx κ c d) (defineMethod h cls d.name md) := by
  intro cn hcn
  change cn ∈ (classWithMethod c d :: κ.classes).map (·.name) ++ κ.scope.runtimeClass.toList at hcn
  simp only [List.map_cons, List.cons_append, List.mem_cons] at hcn
  rcases hcn with he | hcn
  · change cn = c.name at he
    subst cn
    exact ⟨cls, (site.reserveName d.name).methodWrite
      (by simp [nameFreeN, reserveNameCtx, Ctx.declared]) hq hsh⟩
  · obtain ⟨k, old⟩ := sites cn hcn
    exact ⟨k, (old.reserveName d.name).methodWrite
      (by simp [nameFreeN, reserveNameCtx, Ctx.declared]) hq hsh⟩

#print axioms InstanceSite.methodWrite
#print axioms InstanceSite.ivarOnly
end Ratchet.Denote
