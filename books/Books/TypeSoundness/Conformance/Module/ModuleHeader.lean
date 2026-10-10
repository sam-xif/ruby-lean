import Books.TypeSoundness.Checker.Guards.ModuleHeader
import Books.TypeSoundness.Conformance.Module.ModuleReady
import Books.TypeSoundness.Conformance.Module.ModuleDeclared
import Books.TypeSoundness.Conformance.Class.ClassPublish

/-! Publish a fresh module's kind and ordered ancestry while preserving earlier rows.
The table frame forbids activating previously unknown ancestry or dispatch claims. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModule
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem ordered_chain (ho : (h.classPayload? Boot.objectId).isSome = true) :
    NamedChain h₁ [name] (ancestors h₁ h.objs.size) := by
  rw [ancestors_fresh_k]
  exact ⟨named_new (lt_size_of_classPayload ho) ho, trivial⟩

theorem classChains_header {C : CTable} {m : Machine} (hc : ClassReady m.heap)
    (hs : Saturated m.heap) (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hclasses : ClassesOk C m) (hp : ClassChains C m.heap) (ht : ModuleHeaderFrame C name) :
    ClassChains (moduleHeader name :: C) (freshModHeap m.heap Boot.objectId name name) := by
  have old := classChains hc hs hn hclasses hp
  intro c hmem k hk ns hns
  rcases List.mem_cons.mp hmem with rfl | hmem
  · change ancestors? (moduleHeader name :: C) name = some ns at hns
    rw [moduleHeader_ancestors] at hns
    cases hns
    have he := Option.some.inj ((named_new (name := name) (lt_size_of_classPayload ho) ho).symm.trans hk)
    subst k
    exact ordered_chain ho
  · exact old c hmem k hk ns (ht.chain c hmem ns hns)

theorem declared_header {κ : Ctx} {m : Machine} (hnames : NamesOk m.heap) (hc : ClassReady m.heap)
    (hs : Saturated m.heap) (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m)
    (ht : ModuleHeaderFrame κ.classes name) :
    DeclClassOk (moduleHeaderCtx κ name)
      { m with heap := freshModHeap m.heap Boot.objectId name name } := by
  have old := declared (n := { m with heap := freshModHeap m.heap Boot.objectId name name })
    hnames hc.chains hs ho hn rfl hclasses hp
  intro c hmem k hk
  change c ∈ moduleHeader name :: κ.classes at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · have he := Option.some.inj ((named_new (name := name) hc.chains.boot.2.2.2.2 ho).symm.trans hk)
    subst k
    refine ⟨by simp [moduleHeader], (Nat.ne_of_lt hc.chains.boot.1).symm,
      (Nat.ne_of_lt hc.chains.boot.2.1).symm, ?_, by simp [moduleHeader], ?_⟩
    · simp only [freshModHeap_cp_k, Option.map_some, moduleHeader]
    · intro ns hns _
      change ancestors? (moduleHeader name :: κ.classes) name = some ns at hns
      rw [moduleHeader_ancestors] at hns
      cases hns
      change (∀ cn ∈ [name], ∃ j, classNamed? _ cn = some j ∧ (ancestors _ _).contains j = true) ∧
        (∀ cn j, classNamed? _ cn = some j → (ancestors _ _).contains j = true → cn ∈ [name])
      rw [ancestors_fresh_k]
      constructor
      · intro cn hcn
        have he := List.mem_singleton.mp hcn
        subst cn
        exact ⟨m.heap.objs.size, named_new hc.chains.boot.2.2.2.2 ho, by simp⟩
      · intro cn j hcn hj
        have he : j = m.heap.objs.size := by simpa using hj
        subst j
        exact List.mem_singleton.mpr (fresh_name_only hc.constRefs hc.chains.boot.2.2.2.2 hcn)
  · obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := old c hmem k hk
    exact ⟨hroot, hcls, hmod, hism, fun hk hn => hnew hk (ht.newMiss c hmem hn),
      fun ch hch hmix => hchain ch (ht.chain c hmem ch hch) hmix⟩

#print axioms classChains_header
#print axioms declared_header

theorem ownNames_header {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) :
    ClassOwnNames (moduleHeader name :: κ.classes) (freshModHeap m.heap Boot.objectId name name) := by
  apply (ownNames hm.core.classReady.chains.boot.2.2.2.2 hn hm.classes hm.ownNames).cons_empty
  intro k hk
  have he := (named_new (name := name) hm.core.classReady.chains.boot.2.2.2.2
    (hm.runtime hr).classLive).symm.trans hk
  have heq := Option.some.inj he
  subst k
  simp only [ownMethods, freshModHeap_cp_k, Option.map_some, Option.getD_some]

/-- Publish an executed empty module record without an allocator capability. -/
theorem publish_empty {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hs : κ.scope.runtimeClass = some name)
    (hn : unqualifiedClassB name = true)
    (hd : DeclClassOk (moduleHeaderCtx κ name) m)
    (hown : ClassOwnNames (moduleHeader name :: κ.classes) m.heap)
    (hchain : ClassChains (moduleHeader name :: κ.classes) m.heap) :
    StateOk (moduleHeaderCtx κ name) Γ I m := by
  obtain ⟨k, site⟩ := hm.classSites.of_scope hs
  refine { hm with
    classes := ?_
    ownNames := hown
    classChains := hchain
    classSites := ?_
    nested := ?_
    declCls := hd }
  · apply hm.classSites.recontext (κ' := moduleHeaderCtx κ name) _ (fun _ h => h)
    intro cn hcn
    change cn ∈ name :: (κ.classes.map (·.name) ++ κ.scope.runtimeClass.toList) at hcn
    rcases List.mem_cons.mp hcn with rfl | hcn
    · simp [classSiteNames, hs]
    · exact hcn
  · intro old hold
    rcases List.mem_cons.mp hold with rfl | hold
    · exact ⟨k, site.named, by simp [moduleHeader, classHeader], by simp [SingletonRows, moduleHeader, classHeader]⟩
    · exact hm.classes old hold
  · intro owner leaf old hold
    have hne := unqualifiedClassB_ne_path hn owner leaf
    change clsGet? (moduleHeader name :: κ.classes) (owner ++ "::" ++ leaf) = some old at hold
    simp only [clsGet?, List.find?_cons, moduleHeader, classHeader, beq_eq_false_iff_ne.mpr hne] at hold
    exact hm.nested owner leaf old hold

theorem publish_header {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hs : StateOk (moduleBodyCtx κ name) [] .ivar0 n)
    (hn : constOwn m.heap Boot.objectId name = none) (ht : ModuleHeaderFrame κ.classes name)
    (hp : unqualifiedClassB name = true) (hh : n.heap = freshModHeap m.heap Boot.objectId name name) :
    StateOk (moduleHeaderCtx (moduleBodyCtx κ name) name) [] .ivar0 n := by
  apply publish_empty hs rfl hp
  · change DeclClassOk (moduleHeaderCtx κ name) n
    simpa only [DeclClassOk, hh] using declared_header hm.names hm.core.classReady hm.sat
      (hm.runtime hr).classLive hn hm.classes hm.declCls ht
  · rw [hh]; exact ownNames_header (κ := κ) hm hr hn
  · rw [hh]; exact classChains_header hm.core.classReady hm.sat (hm.runtime hr).classLive
      hn hm.classes hm.classChains ht

#print axioms publish_header
end Checker.Soundness.FreshModule
