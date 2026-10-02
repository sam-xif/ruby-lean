import Ratchet.Guards.ModuleHeader
import Denote.Sem.Module.ModuleStateActual
import Denote.Sem.Class.ClassHeaderActual
import Denote.Sem.Class.ClassPublish

/-! Publish the fresh module header (kind, ordered ancestry [name]) over the actual
module-body entry state, preserving earlier rows under the table frame. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String}
local notation "h₁" => heap m name

theorem named_fresh_only (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size) (hl : ConstRefsLive m.heap) {cn : String}
    (hk : classNamed? h₁ cn = some m.heap.objs.size) : cn = name := by
  by_cases hn : cn = name
  · exact hn
  have href := classNamed_constOwn hk
  rw [constOwn_other htop ho ho hn] at href
  exact False.elim ((Nat.lt_irrefl _) (hl cn _ href))

theorem ordered_chain (hc : ChainsIn m.heap) (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    NamedChain h₁ [name] (ancestors h₁ m.heap.objs.size) := by
  rw [ancestors_module hc (htop ▸ lt_size_of_classPayload ho)]
  exact ⟨named_fresh htop ho, trivial⟩

theorem classChains_header {C : CTable} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hclasses : ClassesOk C m) (hp : ClassChains C m.heap) (ht : ModuleHeaderFrame C name) :
    ClassChains (moduleHeader name :: C) h₁ := by
  have old := classChains hc hs htop hn hclasses hp
  intro c hmem k hk ns hns
  rcases List.mem_cons.mp hmem with rfl | hmem
  · change ancestors? (moduleHeader name :: C) name = some ns at hns
    rw [moduleHeader_ancestors] at hns
    cases hns
    have he := Option.some.inj ((named_fresh (name := name) htop ho).symm.trans hk)
    subst k
    exact ordered_chain hc.chains htop ho
  · exact old c hmem k hk ns (ht.chain c hmem ns hns)

theorem declared_header {κ : Ctx} {n : Machine} (hnames : NamesOk m.heap) (hc : ClassReady m.heap)
    (hs : Saturated m.heap) (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hh : n.heap = h₁)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m)
    (ht : ModuleHeaderFrame κ.classes name) : DeclClassOk (moduleHeaderCtx κ name) n := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ lt_size_of_classPayload ho
  have old := declared (n := n) hnames hc.chains hs htop ho hn hh hclasses hp
  intro c hmem k hk
  change c ∈ moduleHeader name :: κ.classes at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · rw [hh] at hk
    have he := Option.some.inj ((named_fresh (name := name) htop ho).symm.trans hk)
    subst k
    refine ⟨by simp [moduleHeader], (Nat.ne_of_lt hc.chains.boot.1).symm,
      (Nat.ne_of_lt hc.chains.boot.2.1).symm, ?_, by simp [moduleHeader], ?_⟩
    · simp only [hh, Heap.classPayload?, get_module hd, namedObject, modPayload, Option.map_some, moduleHeader]
    · intro ns hns _
      change ancestors? (moduleHeader name :: κ.classes) name = some ns at hns
      rw [moduleHeader_ancestors] at hns
      cases hns
      change (∀ cn ∈ [name], ∃ j, classNamed? _ cn = some j ∧ (ancestors _ _).contains j = true) ∧
        (∀ cn j, classNamed? _ cn = some j → (ancestors _ _).contains j = true → cn ∈ [name])
      rw [hh, ancestors_module hc.chains hd]
      constructor
      · intro cn hcn
        have he := List.mem_singleton.mp hcn
        subst cn
        exact ⟨m.heap.objs.size, named_fresh htop ho, by simp⟩
      · intro cn j hcn hj
        have he : j = m.heap.objs.size := by simpa using hj
        subst j
        exact List.mem_singleton.mpr
          (named_fresh_only htop hc.chains.boot.2.2.2.2 hc.constRefs hcn)
  · obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := old c hmem k hk
    exact ⟨hroot, hcls, hmod, hism, fun hk hn => hnew hk (ht.newMiss c hmem hn),
      fun ch hch hmix => hchain ch (ht.chain c hmem ch hch) hmix⟩

theorem ownNames_header {C : CTable} (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassOwnNames C m.heap) :
    ClassOwnNames (moduleHeader name :: C) h₁ := by
  have hol := lt_size_of_classPayload ho
  apply (ownNames htop hol hn ht hp).cons_empty
  intro k hk
  have he := (named_fresh (name := name) htop ho).symm.trans hk
  have heq := Option.some.inj he
  subst k
  simp only [ownMethods, Heap.classPayload?, get_module (htop ▸ hol), namedObject, modPayload]
  rfl

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

variable {κ : Ctx} {Γ : Env} {I : Ty} {body : RubyCore.Expr}
local notation "entry" => machine m name body

theorem header (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true)
    (hplain : unqualifiedClassB name = true) (hframe : ModuleHeaderFrame κ.classes name) :
    StateOk (moduleHeaderCtx (moduleBodyCtx κ name) name) [] .ivar0 entry := by
  have hs := state (body := body) hm hr hf ha ht hq hn hne hreach
  have hc := hm.core.classReady
  have hmain := hm.runtime hr
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  exact publish_empty hs rfl hplain
    (declared_header (κ := moduleBodyCtx κ name) hm.names hc hm.sat htop hmain.classLive hn rfl
      hm.classes hm.declCls hframe)
    (ownNames_header htop hmain.classLive hn hm.classes hm.ownNames)
    (classChains_header hc hm.sat htop hmain.classLive hn hm.classes hm.classChains hframe)

#print axioms declared_header
#print axioms header
end Ratchet.Denote.FreshModuleActual
