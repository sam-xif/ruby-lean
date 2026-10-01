import Denote.Sem.Instance.InstanceTable

/-! Publish executed singleton syntax in the existing class table. Ordinary and singleton
namespaces may share selectors; only collisions at the actual written owner need exclusion. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem ClassesOk_singletonWrite_old {κ : Ctx} {m : Machine} {e : ObjId}
    {name : String} {md : MethodDef} (hp : ClassesOk κ.classes m)
    (sites : ClassSitesOk κ m.heap) (hleaf : (m.heap.get e).eigen = none)
    (hs : ∀ c ∈ κ.classes, ∀ k, classNamed? m.heap c.name = some k →
      (m.heap.get k).eigen = some e → ∀ d ∈ c.smethods, d.name ≠ name) :
    ClassesOk κ.classes { m with heap := defineMethod m.heap e name md } := by
  intro c hc
  obtain ⟨k, hk, methods, single⟩ := hp c hc
  obtain ⟨j, site⟩ := sites.of_class hc
  have hj : j = k := Option.some.inj (site.named.symm.trans hk)
  subst j
  obtain ⟨ec, hec, _, _⟩ := site.metaclass
  have hne : k ≠ e := by
    intro he; subst k; rw [hleaf] at hec; cases hec
  refine ⟨k, by simpa only [classNamed?_defineMethod] using hk, ?_,
    single.methodWrite (hs c hc k hk)⟩
  intro d hd
  obtain ⟨prev, row, rest⟩ := methods d hd
  exact ⟨prev, (ownMethod_defineMethod_other hne).trans row, rest⟩

theorem ClassesOk_publish_singleton {κ : Ctx} {m : Machine} {c : Cls} {d : Defn}
    {k e : ObjId} {md : MethodDef} (hp : ClassesOk κ.classes m)
    (sites : ClassSitesOk κ m.heap) (hc : c ∈ κ.classes)
    (hk : classNamed? m.heap c.name = some k) (he : (m.heap.get k).eigen = some e)
    (hs : ∀ old ∈ κ.classes, ∀ j, classNamed? m.heap old.name = some j →
      (m.heap.get j).eigen = some e → ∀ prev ∈ old.smethods, prev.name ≠ d.name)
    (hparams : md.params = toRubyParams d.params) (hbody : md.body = toRuby d.body)
    (hu : md.undefined = false) (hcode : SingletonMethodCode k e md) :
    ClassesOk ({ c with smethods := d :: c.smethods } :: κ.classes)
      { m with heap := defineMethod m.heap e d.name md } := by
  obtain ⟨j, site⟩ := sites.of_class hc
  have hj : j = k := Option.some.inj (site.named.symm.trans hk)
  subst j
  have hleaf : (m.heap.get e).eigen = none := by
    simpa only [classOf, he] using site.metaLeaf
  have old := ClassesOk_singletonWrite_old (md := md) hp sites hleaf hs
  intro c' hc'
  rcases List.mem_cons.mp hc' with rfl | hc'
  · obtain ⟨j, hj, methods, single⟩ := old c hc
    have hjk : j = k := Option.some.inj (hj.symm.trans ((classNamed?_defineMethod ..).trans hk))
    subst j
    refine ⟨k, hj, methods, ?_⟩
    intro prev hprev
    rcases List.mem_cons.mp hprev with rfl | hprev
    · refine ⟨e, md, (Proof.get_defineMethod_eigen ..).trans he,
        (Proof.get_defineMethod_eigen ..).trans hleaf, ?_, hparams, hbody, hu, hcode⟩
      apply ownMethod_defineMethod_self
      have hf := site.eigen_front he
      cases hp : m.heap.classPayload? e <;> simp_all [classFrontB]
    · exact single prev hprev
  · exact old c' hc'

#print axioms ClassesOk_singletonWrite_old
#print axioms ClassesOk_publish_singleton
end Ratchet.Denote
