import Books.TypeSoundness.Conformance.Module.ModuleMetadataActual
import Books.TypeSoundness.Conformance.Module.ModuleQueriesActual
import Books.TypeSoundness.Conformance.Class.ClassDeclaredActual

/-! Preserve published class declarations/own names/chains through actual module registration. -/

set_option autoImplicit false
namespace Checker.Soundness.FreshModuleActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

variable {m : Machine} {name : String} 
local notation "h₁" => heap m name

variable {κ : Ctx} {n : Machine}

theorem declared (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId) (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = heap m name)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m) : DeclClassOk κ n := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  intro c hmem k hk
  have hol := hc.boot.2.2.2.2
  obtain ⟨j, hj, _⟩ := hclasses c hmem
  have hj' := named_old  htop hol hn hj
  rw [← hh] at hj'
  have heq : j = k := Option.some.inj (hj'.symm.trans hk)
  subst k
  have hjl := Subclass.named_live hj
  have hcl := ClsGrow.classOf_lt hc hjl
  obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := hp c hmem j hj
  refine ⟨?_, hcls, hmod, ?_, ?_, ?_⟩
  · rw [hh, ancestors_old hc hs hd hjl]; exact hroot
  · rw [hh, module_old hd hjl]; exact hism
  · intro hkind hnone
    obtain ⟨hfound, hmiss⟩ := hnew hkind hnone
    refine ⟨?_, ?_⟩
    · intro owner md hm
      rw [hh, classOf_old hd hjl, method_old hc hs hd hcl] at hm
      obtain ⟨hb, hu, hv, hpre, hshadow⟩ := hfound owner md hm
      refine ⟨hb, hu, hv, hpre, ?_⟩
      rw [hh, classOf_old hd hjl, shadow_before_old hnames hc hs hd hcl]
      exact hshadow
    · simpa only [hh, classOf_old hd hjl, method_old hc hs hd hcl] using hmiss
  · intro ch hch hmix
    obtain ⟨hpos, hneg⟩ := hchain ch hch hmix
    refine ⟨?_, ?_⟩
    · intro cn hcn
      obtain ⟨k, hk, ha⟩ := hpos cn hcn
      refine ⟨k, ?_, ?_⟩
      · rw [hh]; exact named_old htop hol hn hk
      · rw [hh, ancestors_old hc hs hd hjl]; exact ha
    · intro cn k hk ha
      rw [hh, ancestors_old hc hs hd hjl] at ha
      have hkl := ClsGrow.ancestors_mem_lt hc hjl k (List.contains_iff_mem.mp ha)
      rw [hh] at hk
      exact hneg cn k (named_old_back htop ho hkl hk) ha

theorem ownNames {C : CTable}
    (htop : m.lexicalNamespace = Boot.objectId) (ho : Boot.objectId < m.heap.objs.size) (hn : constOwn m.heap Boot.objectId name = none)
    (hc : ClassesOk C m) (hp : ClassOwnNames C m.heap) :
    ClassOwnNames C (heap m name) := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ ho
  apply hp.transport
  · intro c hmem k hk
    obtain ⟨j, hj, _⟩ := hc c hmem
    have he := (named_old  htop ho hn hj).symm.trans hk
    exact Option.some.inj he ▸ hj
  · intro k p hm
    simpa only [ownMethods, own_methods hd] using hm

theorem classChains {C : CTable} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId) (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassChains C m.heap) :
    ClassChains C (heap m name) := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  intro c hmem k hk ns hns
  obtain ⟨j, hj, _⟩ := ht c hmem
  have he := (named_old  htop hc.chains.boot.2.2.2.2 hn hj).symm.trans hk
  have heq := Option.some.inj he
  subst k
  rw [ancestors_old hc.chains hs hd (Subclass.named_live hj)]
  exact (hp c hmem j hj ns hns).names (fun _ _ hj => named_old htop hc.chains.boot.2.2.2.2 hn hj)

#print axioms declared
#print axioms ownNames
#print axioms classChains
end Checker.Soundness.FreshModuleActual
