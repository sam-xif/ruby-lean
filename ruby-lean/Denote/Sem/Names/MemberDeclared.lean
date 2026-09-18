import Denote.Sem.Names.MemberFrame

/-! Installing an ordinary instance member preserves allocator metadata and named ancestry.
Changing new/method_missing needs a different contract, not this transport. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem DeclClassOk.methodWrite {κ : Ctx} {m : Machine} {cls : ObjId} {name : String}
    {md : MethodDef} (hp : DeclClassOk κ m)
    (hn : "new" ≠ name) (hm : "method_missing" ≠ name) :
    DeclClassOk κ { m with heap := defineMethod m.heap cls name md } := by
  have hmodule (k : ObjId) :
      ((defineMethod m.heap cls name md).classPayload? k).map (·.isModule) =
        (m.heap.classPayload? k).map (·.isModule) := by
    have h := congrArg (Option.map Prod.snd) (Proof.clsName_defineMethod m.heap cls k name md)
    simpa only [Option.map_map, Function.comp_def] using h
  simpa only [DeclClassOk, classNamed?_defineMethod, Proof.ancestors_defineMethod,
    hmodule, Proof.classOf_defineMethod, methodOn_defineMethod _ _ _ _ _ _ hn,
    methodOn_defineMethod _ _ _ _ _ _ hm, crubyShadow_defineMethod] using hp

theorem DeclClassOk.publish_member {κ : Ctx} {m : Machine} {c : Cls} {d : Defn}
    (hp : DeclClassOk κ m) (hc : c ∈ κ.classes)
    (ht : DeclLookupFrame κ.classes (classWithMethod c d :: κ.classes)) :
    DeclClassOk (instanceDeclCtx κ c d) m := by
  intro old hold k hk
  change old ∈ classWithMethod c d :: κ.classes at hold
  rcases List.mem_cons.mp hold with rfl | hold
  · obtain ⟨hr, hcl, hm, hi, hn, ha⟩ := hp c hc k hk
    exact ⟨hr, hcl, hm, hi, fun h => hn (ht.newMiss c hc h),
      fun ch hch hmix => ha ch (ht.chain c hc ch hch) hmix⟩
  · obtain ⟨hr, hcl, hm, hi, hn, ha⟩ := hp old hold k hk
    exact ⟨hr, hcl, hm, hi, fun h => hn (ht.newMiss old hold h),
      fun ch hch hmix => ha ch (ht.chain old hold ch hch) hmix⟩

theorem NestedClassesOk.publish_member {C : CTable} {m : Machine} {c : Cls} {d : Defn}
    (hp : NestedClassesOk C m) (hn : unqualifiedClassB c.name = true) :
    NestedClassesOk (classWithMethod c d :: C) m := by
  intro owner leaf old hlook
  have hne := unqualifiedClassB_ne_path hn owner leaf
  simp only [clsGet?, List.find?_cons, classWithMethod, beq_eq_false_iff_ne.mpr hne] at hlook
  exact hp owner leaf old hlook

theorem NestedClassesOk.methodWrite {C : CTable} {m : Machine} {cls : ObjId}
    {name : String} {md : MethodDef} (hp : NestedClassesOk C m) :
    NestedClassesOk C { m with heap := defineMethod m.heap cls name md } := by
  simpa only [NestedClassesOk, isClassRefNamed, classNamed?_defineMethod,
    Proof.constLookupFrom_defineMethod] using hp

#print axioms DeclClassOk.methodWrite
#print axioms DeclClassOk.publish_member
end Ratchet.Denote
