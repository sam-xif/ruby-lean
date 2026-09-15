import Ratchet.ClassCtx
import Denote.Sem.MethodInstall

/-! Publish an actually installed instance method. Preserve old records at other owners,
and at this owner only when their method names are untouched. Names may alias one owner. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem namedClass_payload {h : Heap} {cn : String} {k : ObjId}
    (hk : classNamed? h cn = some k) : (h.classPayload? k).isSome = true := by
  unfold classNamed? at hk
  split at hk
  · split at hk
    · rename_i hp; cases hk; exact hp
    · cases hk
  · cases hk

theorem ownMethod_defineMethod_other {h : Heap} {cls k : ObjId} {name mn : String}
    {md : MethodDef} (hk : k ≠ cls) :
    ((defineMethod h cls name md).classPayload? k).bind
        (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
      (h.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) := by
  simp only [Heap.classPayload?, heap_get_defineMethod_ne hk]

theorem ClassesOk_empty_class {c : Cls} {m : Machine} {k : ObjId}
    (hk : classNamed? m.heap c.name = some k) (he : c.methods = []) : ClassesOk [c] m := by
  intro old hold
  have ho := List.mem_singleton.mp hold
  subst old
  refine ⟨k, hk, ?_⟩
  intro d hd; rw [he] at hd; cases hd

/-- A same-name method at a different *heap owner* is untouched. Comparing class names
alone is insufficient because two names can denote the same class object. -/
theorem ClassesOk_methodWrite_old {C : CTable} {m : Machine} {cls : ObjId}
    {name : String} {md : MethodDef} (hp : ClassesOk C m)
    (hs : ∀ c ∈ C, classNamed? m.heap c.name = some cls →
      ∀ d ∈ c.methods, d.name ≠ name) :
    ClassesOk C { m with heap := defineMethod m.heap cls name md } := by
  intro c hc
  obtain ⟨k, hk, hmethods⟩ := hp c hc
  refine ⟨k, by rw [classNamed?_defineMethod]; exact hk, ?_⟩
  intro d hd
  obtain ⟨prev, hfind, hrest⟩ := hmethods d hd
  refine ⟨prev, ?_, hrest⟩
  by_cases he : k = cls
  · subst k
    rw [ownMethod_defineMethod_ne _ _ _ _ _ _ (hs c hc hk d hd)]
    exact hfind
  · rw [ownMethod_defineMethod_other he]
    exact hfind

theorem ClassesOk_publish_instance {C : CTable} {c : Cls} {d : Defn} {m : Machine}
    {cls : ObjId} {md : MethodDef} (hC : ClassesOk C m) (hc : ClassesOk [c] m)
    (hk : classNamed? m.heap c.name = some cls)
    (hf : ∀ old ∈ c.methods, old.name ≠ d.name)
    (hs : ∀ old ∈ C, classNamed? m.heap old.name = some cls →
      ∀ method ∈ old.methods, method.name ≠ d.name)
    (hp : md.params = toRubyParams d.params) (hb : md.body = toRuby d.body)
    (hu : md.undefined = false) (hcode : InstanceMethodCode cls d.name md) :
    ClassesOk (classWithMethod c d :: C) { m with heap := defineMethod m.heap cls d.name md } := by
  have hCold := ClassesOk_methodWrite_old (md := md) hC hs
  have htarget : ClassesOk [c] { m with heap := defineMethod m.heap cls d.name md } :=
    ClassesOk_methodWrite_old hc (by
      intro old ho _ method hm
      have he := List.mem_singleton.mp ho
      subst old
      exact hf method hm)
  intro old ho
  rcases List.mem_cons.mp ho with he | ho
  · subst old
    obtain ⟨k, hk', hm⟩ := htarget c (List.mem_singleton_self _)
    rw [classNamed?_defineMethod, hk] at hk'
    have he : cls = k := Option.some.inj hk'
    subst k
    refine ⟨cls, by rw [classNamed?_defineMethod]; exact hk, ?_⟩
    intro method hmeth
    rcases List.mem_cons.mp hmeth with he | hmeth
    · subst method
      exact ⟨md, ownMethod_defineMethod_self _ _ _ _ (namedClass_payload hk), hp, hb, hu, hcode⟩
    · exact hm method hmeth
  · exact hCold old ho

theorem DefsOk_methodWrite_other {D : DefTable} {m : Machine} {cls : ObjId}
    {name : String} {md : MethodDef} (hp : DefsOk D m) (hc : cls ≠ Boot.objectId) :
    DefsOk D { m with heap := defineMethod m.heap cls name md } := by
  intro d hd
  obtain ⟨prev, hf, hrest⟩ := hp d hd
  exact ⟨prev, (ownMethod_defineMethod_other hc.symm).trans hf, hrest⟩

/-- Publication derives the code/def tables and all ordinary heap/frame fields. Constructor
and nested-name contracts remain explicit obligations for the class rule, not inferred from
the method's signature or from an empty own-method table. -/
theorem StateOk_publish_instance {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {d : Defn} {cls : ObjId} {md : MethodDef}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (ha : κ.asms = [])
    (hc : ClassesOk [c] m) (hk : classNamed? m.heap c.name = some cls)
    (hsite : InstanceSite κ c.name cls m.heap)
    (hobj : cls ≠ Boot.objectId) (hf : ∀ old ∈ c.methods, old.name ≠ d.name)
    (hs : ∀ old ∈ κ.classes, classNamed? m.heap old.name = some cls →
      ∀ method ∈ old.methods, method.name ≠ d.name)
    (hp : md.params = toRubyParams d.params) (hb : md.body = toRuby d.body)
    (hu : md.undefined = false) (hcode : InstanceMethodCode cls d.name md)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name)
    (hnested : NestedClassesOk (classWithMethod c d :: κ.classes)
      { m with heap := defineMethod m.heap cls d.name md })
    (hdecl : DeclClassOk (instanceDeclCtx κ c d)
      { m with heap := defineMethod m.heap cls d.name md })
    (hown : ClassOwnNames (classWithMethod c d :: κ.classes) (defineMethod m.heap cls d.name md)) :
    StateOk (instanceDeclCtx κ c d) Γ I { m with heap := defineMethod m.heap cls d.name md } := by
  have hr : ReframeFO (reserveNameCtx κ d.name) I :=
    ⟨ht.spine, ht.self, ht.block, ht.consts, ht.paths⟩
  exact StateOk_methodWrite_tables (StateOk_reserveName hm d.name) hr hΓ ha
    (by simp [nameFreeN, reserveNameCtx, Ctx.declared]) hmiss hquiet
    (ClassesOk_publish_instance hm.classes hc hk hf hs hp hb hu hcode)
    (hm.classSites.publish_instance hsite hquiet)
    (DefsOk_methodWrite_other hm.defs hobj) hnested hdecl hown

#print axioms ClassesOk_methodWrite_old
#print axioms ClassesOk_publish_instance
#print axioms StateOk_publish_instance
end Ratchet.Denote
