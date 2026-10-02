import Ratchet.Guards.SingletonCtx
import Denote.Sem.Singleton.SingletonTable
import Denote.Sem.Names.MemberDeclared

/-! Publication retains existing class ancestry, constants and ordinary selector bounds.
The table guard prevents a stale class snapshot from activating an unsupported claim. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem ClassSitesOk.publish_singleton {κ : Ctx} {c : Cls} {d : Defn} {e : ObjId}
    {h : Heap} {md : MethodDef} (sites : ClassSitesOk κ h) (hc : c ∈ κ.classes)
    (hq : "method_added" ≠ d.name) (hsh : singletonHookName ≠ d.name)
    (hinh : "inherited" ≠ d.name) :
    ClassSitesOk (singletonDeclCtx κ c d) (defineMethod h e d.name md) := by
  intro cn hcn
  change cn ∈ (classWithSingleton c d :: κ.classes).map (·.name) ++ κ.scope.runtimeClass.toList at hcn
  simp only [List.map_cons, List.cons_append, List.mem_cons] at hcn
  have old : cn ∈ classSiteNames κ := by
    rcases hcn with rfl | hcn
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    · exact hcn
  obtain ⟨k, site⟩ := sites cn old
  exact ⟨k, (site.reserveName d.name).methodWrite
    (by simp [nameFreeN, reserveNameCtx, Ctx.declared]) hq hsh hinh⟩

theorem DeclClassOk.publish_singleton {κ : Ctx} {m : Machine} {c : Cls} {d : Defn}
    (hp : DeclClassOk κ m) (hc : c ∈ κ.classes)
    (ht : DeclLookupFrame κ.classes (classWithSingleton c d :: κ.classes)) :
    DeclClassOk (singletonDeclCtx κ c d) m := by
  intro old hold k hk
  change old ∈ classWithSingleton c d :: κ.classes at hold
  rcases List.mem_cons.mp hold with rfl | hold
  · obtain ⟨hr, hcl, hm, hi, hn, ha⟩ := hp c hc k hk
    exact ⟨hr, hcl, hm, hi, fun hk h => hn hk (ht.newMiss c hc h),
      fun ch hch hmix => ha ch (ht.chain c hc ch hch) hmix⟩
  · obtain ⟨hr, hcl, hm, hi, hn, ha⟩ := hp old hold k hk
    exact ⟨hr, hcl, hm, hi, fun hk h => hn hk (ht.newMiss old hold h),
      fun ch hch hmix => ha ch (ht.chain old hold ch hch) hmix⟩

theorem NestedClassesOk.publish_singleton {C : CTable} {m : Machine} {c : Cls} {d : Defn}
    (hp : NestedClassesOk C m) (hn : unqualifiedClassB c.name = true) :
    NestedClassesOk (classWithSingleton c d :: C) m := by
  intro owner leaf old hlook
  have hne := unqualifiedClassB_ne_path hn owner leaf
  simp only [clsGet?, List.find?_cons, classWithSingleton, beq_eq_false_iff_ne.mpr hne] at hlook
  exact hp owner leaf old hlook

theorem ClassChains.publish_singleton {C : CTable} {h : Heap} {c : Cls} {d : Defn}
    (hp : ClassChains C h) (hc : c ∈ C)
    (ht : DeclLookupFrame C (classWithSingleton c d :: C)) :
    ClassChains (classWithSingleton c d :: C) h := by
  intro old hold k hk ns hns
  rcases List.mem_cons.mp hold with rfl | hold
  · exact hp c hc k hk ns (ht.chain c hc ns hns)
  · exact hp old hold k hk ns (ht.chain old hold ns hns)

theorem ClassOwnNames.publish_singleton {κ : Ctx} {h : Heap} {c : Cls} {d : Defn}
    {e : ObjId} {md : MethodDef} (hp : ClassOwnNames κ.classes h)
    (sites : ClassSitesOk κ h) (hc : c ∈ κ.classes) (hleaf : (h.get e).eigen = none) :
    ClassOwnNames (classWithSingleton c d :: κ.classes) (defineMethod h e d.name md) := by
  have hw : ClassOwnNames κ.classes (defineMethod h e d.name md) := by
    apply hp.methodWrite
    intro old hold hk
    obtain ⟨ec, hec, _, _⟩ := (sites.at_class hold hk).metaclass
    rw [hleaf] at hec
    cases hec
  intro old hold k hk p hm
  rcases List.mem_cons.mp hold with rfl | hold
  · exact ownNames_cons_mono _ (hw c hc k hk p hm)
  · exact ownNames_cons_mono _ (hw old hold k hk p hm)

end Ratchet.Denote
