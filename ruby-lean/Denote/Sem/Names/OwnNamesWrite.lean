import Denote.Sem.Names.OwnNames
import Denote.Sem.Names.MemberFrame

/-! Generic own-selector transport through real method installation. The written selector
must be allowed at every declared name for its physical owner, not merely globally reserved. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

/-- A write changes only its physical owner's own table. All other entries came from
the old heap, including builtin, prelude and undefined entries. -/
theorem ownMethods_defineMethod_mem {h : Heap} {cls k : ObjId} {name : String}
    {md : MethodDef} {p : String × MethodDef}
    (hp : p ∈ ownMethods (defineMethod h cls name md) k) :
    (k = cls ∧ p = (name, md)) ∨ p ∈ ownMethods h k := by
  unfold defineMethod at hp
  split at hp
  · rename_i cp hc
    by_cases hk : k = cls
    · subst k
      have hb : cls < h.objs.size := lt_size_of_classPayload (by rw [hc]; rfl)
      simp only [ownMethods, Heap.classPayload?, Heap.setClassPayload, Heap.get, Heap.set,
        Proof.objs_getD_set!_self _ _ _ hb, Option.map_some, Option.getD_some,
        List.mem_cons, List.mem_filter] at hp
      rcases hp with he | ⟨hm, _⟩
      · exact Or.inl ⟨rfl, he⟩
      · exact Or.inr (by simpa [ownMethods, hc] using hm)
    · right
      simpa only [ownMethods, Heap.classPayload?, Heap.setClassPayload, Heap.get, Heap.set,
        Proof.objs_getD_set!_ne _ _ _ _ hk] using hp
  · exact Or.inr hp

theorem ClassOwnNames.methodWrite {C : CTable} {h : Heap} {cls : ObjId}
    {name : String} {md : MethodDef} (hp : ClassOwnNames C h)
    (hw : ∀ c ∈ C, classNamed? h c.name = some cls → name ∈ ownNames C c.name) :
    ClassOwnNames C (defineMethod h cls name md) := by
  intro c hc k hk p hm
  rw [classNamed?_defineMethod] at hk
  rcases ownMethods_defineMethod_mem hm with ⟨rfl, rfl⟩ | hold
  · exact hw c hc hk
  · exact hp c hc k hk p hold

/-- Add a new snapshot of an already declared class. Its old selectors remain in the
union even when the snapshot was built from an earlier record. -/
theorem ClassOwnNames.publish {C : CTable} {h : Heap} {c : Cls} (d : Defn)
    (hp : ClassOwnNames C h) (hc : c ∈ C) :
    ClassOwnNames (classWithMethod c d :: C) h := by
  intro old hold k hk p hm
  rcases List.mem_cons.mp hold with rfl | hold
  · exact ownNames_cons_mono _ (hp c hc k hk p hm)
  · exact ownNames_cons_mono _ (hp old hold k hk p hm)

theorem ClassOwnNames.publish_instance {C : CTable} {h : Heap} {c : Cls} {d : Defn}
    {cls : ObjId} {md : MethodDef} (hp : ClassOwnNames C h) (hc : c ∈ C)
    (hs : ∀ old ∈ C, classNamed? h old.name = some cls → old.name = c.name) :
    ClassOwnNames (classWithMethod c d :: C) (defineMethod h cls d.name md) := by
  apply (hp.publish d hc).methodWrite
  intro old hold hk
  rcases List.mem_cons.mp hold with rfl | hold
  · exact ownNames_publish C c d
  · rw [hs old hold hk]
    exact ownNames_publish C c d

theorem memberOwnersB_sound {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k : ObjId} (hm : StateOk κ Γ I m)
    (hc : c ∈ κ.classes) (hk : classNamed? m.heap c.name = some k)
    (hf : memberOwnersB κ c = true) :
    ∀ old ∈ κ.classes, classNamed? m.heap old.name = some k → old.name = c.name := by
  intro old hold holdk
  have hrow := List.all_eq_true.mp hf old hold
  simp only [Bool.or_eq_true, beq_iff_eq] at hrow
  rcases hrow with (he | ha) | ha
  · exact he
  · obtain ⟨j, site⟩ := hm.classSites.of_class hc
    have he := Option.some.inj (site.named.symm.trans hk)
    subst j
    exact False.elim ((classApartB_ne hm.declCls hc hk holdk site.front ha) rfl)
  · obtain ⟨j, site⟩ := hm.classSites.of_class hold
    have he := Option.some.inj (site.named.symm.trans holdk)
    subst j
    exact False.elim ((classApartB_ne hm.declCls hold holdk hk site.front ha) rfl)

#print axioms ClassOwnNames.publish_instance
#print axioms memberOwnersB_sound
end Ratchet.Denote
