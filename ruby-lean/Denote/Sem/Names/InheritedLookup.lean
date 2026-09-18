import Denote.Sem.Names.OwnLookup

/-! Declared ancestry plus owner-local absence supplies the actual inherited lookup.
No physical prefix or lookup equality is assumed. Code is not a proof of its annotation:
the call layer must still consume the full body proof and check native interception. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem ClassChains.before_owner {C : CTable} {h : Heap} {c : Cls} {r : ObjId}
    {pre post : List String} {owner : String} (hp : ClassChains C h)
    (hc : c ∈ C) (hr : classNamed? h c.name = some r)
    (ha : ancestors? C c.name = some (pre ++ owner :: post)) :
    ∃ before k after, ancestors h r = before ++ k :: after ∧ NamedChain h pre before ∧
      classNamed? h owner = some k ∧ NamedChain h (post ++ rootAncestors) after := by
  have hs := hp c hc r hr _ ha
  have hs' : NamedChain h (pre ++ owner :: (post ++ rootAncestors)) (ancestors h r) := by
    simpa only [List.append_assoc, List.cons_append] using hs
  exact hs'.split

theorem declared_inherited_code {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {recvClass owner : Cls} {d : Defn} {r : ObjId} {pre post : List String}
    (hm : StateOk κ Γ I m) (hrc : recvClass ∈ κ.classes)
    (hr : classNamed? m.heap recvClass.name = some r)
    (hoc : owner ∈ κ.classes) (hd : d ∈ owner.methods)
    (ha : ancestors? κ.classes recvClass.name = some (pre ++ owner.name :: post))
    (hn : ∀ cn ∈ pre, ∃ old ∈ κ.classes, old.name = cn ∧ d.name ∉ ownNames κ.classes cn) :
    ∃ k md, classNamed? m.heap owner.name = some k ∧
      Interp.methodOn m.heap r d.name = some (k, md) ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      md.undefined = false ∧ InstanceMethodCode k d.name md := by
  apply classesOk_methodOn_after_prefix hm.classes hm.ownNames hoc hd
  intro k hk
  obtain ⟨before, j, after, he, hpre, hj, _⟩ := hm.classChains.before_owner hrc hr ha
  have hkj := Option.some.inj (hj.symm.trans hk)
  subst j
  refine ⟨before, after, he, ?_⟩
  intro j hmem
  obtain ⟨cn, hcn, hj⟩ := hpre.cover hmem
  obtain ⟨old, hold, hname, hmiss⟩ := hn cn hcn
  exact ⟨old, hold, by simpa only [hname] using hj, by simpa only [hname] using hmiss⟩

#print axioms declared_inherited_code
end Ratchet.Denote
