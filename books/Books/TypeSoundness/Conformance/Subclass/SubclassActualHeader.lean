import Books.TypeSoundness.Conformance.Class.ClassHeaderStateActual
import Books.TypeSoundness.Checker.Guards.SubclassHeader

/-! Publish a fresh subclass header on the actual named/attached heap. The parent's
allocator, dispatch and named chain transfer through the prepended fresh class. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof
variable {m : Machine} {name : String} {e p : ObjId}
local notation "h₁" => heap m name e p

theorem flags_of_plain {h : Heap} {k : ObjId} (ha : PlainAllocator h k) :
    objectClassFlagsB h k = true := by
  obtain ⟨cp, hp, hat, hin, har, hun⟩ := ha.metadata
  simp [objectClassFlagsB, Heap.classPayload?, hp, har, hun]

theorem plainSub (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (ha : PlainAllocator m.heap p) :
    PlainAllocator h₁ m.heap.objs.size := by
  have hb := hc.bootEnd
  have hne (k : ObjId) (hk : k ≤ Boot.yielderId) : m.heap.objs.size ≠ k :=
    (Nat.ne_of_lt (Nat.lt_of_le_of_lt hk hb)).symm
  have hchain := ancestors_class (name := name) (e := e) hc.chains hs hd ha.live
  refine ⟨?_, hne _ (by decide), hne _ (by decide), hne _ (by decide), hne _ (by decide),
    ?_, ?_, ?_, allocator_ready hd (flags_of_plain ha), ?_, ?_⟩
  · rw [size]; exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  · simp only [Heap.classPayload?, get_class hd, namedObject, freshClassPayload, Option.map_some]
  · rw [hchain]
    exact List.contains_iff_mem.mpr (List.mem_cons_of_mem _ (List.contains_iff_mem.mp ha.rooted))
  · simpa only [Builtins.allocatableCore, hchain, List.find?_cons,
      beq_eq_false_iff_ne.mpr (hne Boot.stringId (by decide)),
      beq_eq_false_iff_ne.mpr (hne Boot.arrayId (by decide)),
      beq_eq_false_iff_ne.mpr (hne Boot.hashId (by decide)),
      beq_eq_false_iff_ne.mpr (hne Boot.exceptionId (by decide)), Bool.false_or, Bool.false_eq_true,
      ite_false] using ha.noCore
  · rw [hchain, List.any_cons, ha.noPayload, Bool.or_false]
    simp [Builtins.payloadCoreClasses]
    (repeat' apply And.intro) <;> exact hne _ (by decide)
  · have hp := ha.plainChain
    simp only [List.all_cons, Bool.and_eq_true] at hp
    rw [hchain]
    simp only [List.all_cons, Bool.and_eq_true]
    have hfresh : (!constructBlockers.contains m.heap.objs.size) = true := by
      simp [constructBlockers]
      (repeat' apply And.intro) <;> exact hne _ (by decide)
    exact ⟨hfresh, hfresh, hp.2⟩

#print axioms plainSub

theorem named_fresh_onlyAt (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size) (hl : ConstRefsLive m.heap) {cn : String}
    (hk : classNamed? h₁ cn = some m.heap.objs.size) : cn = name := by
  by_cases hn : cn = name
  · exact hn
  have href := classNamed_constOwn hk
  rw [constOwn_other htop ho ho hn] at href
  exact False.elim ((Nat.lt_irrefl _) (hl cn _ href))

theorem ordered_chainSub {ns : List String} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hpl : p < m.heap.objs.size)
    (hp : NamedChain m.heap ns (ancestors m.heap p)) :
    NamedChain h₁ (name :: ns) (ancestors h₁ m.heap.objs.size) := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ lt_size_of_classPayload ho
  rw [ancestors_class hc.chains hs hd hpl]
  exact ⟨named_fresh htop ho,
    hp.names (fun _ _ hk => named_old (p := p) htop (lt_size_of_classPayload ho) hn hk)⟩

theorem named_chainSub {ns : List String} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hpl : p < m.heap.objs.size)
    (hpos : ∀ cn ∈ ns, ∃ k, classNamed? m.heap cn = some k ∧ (ancestors m.heap p).contains k = true)
    (hneg : ∀ cn k, classNamed? m.heap cn = some k → (ancestors m.heap p).contains k = true → cn ∈ ns) :
    (∀ cn ∈ name :: ns, ∃ k, classNamed? h₁ cn = some k ∧
      (ancestors h₁ m.heap.objs.size).contains k = true) ∧
    (∀ cn k, classNamed? h₁ cn = some k → (ancestors h₁ m.heap.objs.size).contains k = true →
      cn ∈ name :: ns) := by
  have hol := lt_size_of_classPayload ho
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hol
  constructor
  · intro cn hcn
    rcases List.mem_cons.mp hcn with rfl | hcn
    · exact ⟨m.heap.objs.size, named_fresh htop ho,
        by simp only [ancestors_class hc.chains hs hd hpl, List.contains_cons, beq_self_eq_true,
          Bool.true_or]⟩
    · obtain ⟨k, hk, ha⟩ := hpos cn hcn
      refine ⟨k, named_old (p := p) htop hol hn hk, ?_⟩
      rw [ancestors_class hc.chains hs hd hpl]
      exact List.contains_iff_mem.mpr (List.mem_cons_of_mem _ (List.contains_iff_mem.mp ha))
  · intro cn k hk ha
    rw [ancestors_class hc.chains hs hd hpl] at ha
    rcases List.mem_cons.mp (List.contains_iff_mem.mp ha) with rfl | hmem
    · rw [named_fresh_onlyAt htop hol hc.constRefs hk]
      exact List.mem_cons_self
    · have hkl := ClsGrow.ancestors_mem_lt hc.chains hpl k hmem
      exact List.mem_cons_of_mem _
        (hneg cn k (named_old_back (p := p) htop ho hkl hk) (List.contains_iff_mem.mpr hmem))

theorem new_dispatchSub (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hel : e < m.heap.objs.size)
    (hpl : p < m.heap.objs.size)
    (he : (m.heap.get p).eigen = some e) (hne : name.isEmpty = false)
    (hq : classNativeQuietB name "new" = true) (hlmain : Boot.mainId < m.heap.objs.size)
    (hD : NewDispatch m.heap (classOf m.heap (.ref p))) :
    NewDispatch h₁ (classOf h₁ (.ref m.heap.objs.size)) := by
  obtain ⟨hn₁, hn₂⟩ := classNativeQuietB_sound hq
  have hm (mn : String) : Interp.methodOn h₁ (classOf h₁ (.ref m.heap.objs.size)) mn =
      Interp.methodOn m.heap (classOf m.heap (.ref p)) mn := by
    rw [classOf_class hd, method_eigen hc hs hd hel]
    simp only [classOf, he]
  refine ⟨?_, by simpa only [hm] using hD.present⟩
  intro owner md hl
  obtain ⟨hb, hu, hv, hp, hsh⟩ := hD.found owner md ((hm "new").symm ▸ hl)
  refine ⟨hb, hu, hv, hp, ?_⟩
  rw [classOf_class hd]
  apply shadow_before_source hnames hc hs hd hel hne hn₁ hn₂ (classNativeQuietB_singleton hq) hlmain hpl
  simpa only [source, Subclass.source, if_neg (Nat.succ_ne_self _), ite_true, classOf, he] using hsh

#print axioms ordered_chainSub
#print axioms named_chainSub
#print axioms new_dispatchSub

section Publish
variable {κ : Ctx} {Γ : Env} {I : Ty} {n : Machine} {c : Cls}

theorem declared_headerSub (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some p)
    (ha : PlainAllocator m.heap p) (he : (m.heap.get p).eigen = some e)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hq : classNativeQuietB name "new" = true) (hnew : smroGet? κ.classes c.name "new" = none)
    (ht : SubclassHeaderFrame κ.classes name c.name) (hh : n.heap = h₁) :
    DeclClassOk (subclassHeaderCtx κ name c.name) n := by
  have ready := hm.core.classReady
  have hmain := hm.runtime hr
  have ho := hmain.classLive
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hol := lt_size_of_classPayload ho
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hol
  have hel := ready.chains.eigen _ ha.live _ he
  have old := declared hm.names ready.chains hm.sat htop ho hn hh hm.classes hm.declCls
  have parentDecl := hm.declCls c hc p hp
  have hkind : c.isModule = false := Option.some.inj (parentDecl.2.2.2.1.symm.trans ha.module)
  have newDispatch : NewDispatch m.heap (classOf m.heap (.ref p)) := ⟨
    (parentDecl.2.2.2.2.1 hkind hnew).1, (parentDecl.2.2.2.2.1 hkind hnew).2⟩
  obtain ⟨ns, hparent, hchild⟩ := ht.chain
  intro record hrecord k hk
  change record ∈ subclassHeader name c.name :: κ.classes at hrecord
  rcases List.mem_cons.mp hrecord with rfl | hrecord
  · change classNamed? n.heap name = some k at hk
    rw [hh, named_fresh htop ho] at hk
    cases hk
    have shape := plainSub (name := name) (e := e) ready hm.sat hd ha
    have dispatch := new_dispatchSub (name := name) hm.names ready.chains hm.sat hd hel ha.live he hne hq
      hmain.live newDispatch
    rw [← hh] at shape dispatch
    refine ⟨fun _ => shape.rooted, shape.notClass, shape.notModule, shape.module,
      fun _ _ => ⟨dispatch.found, dispatch.present⟩, ?_⟩
    intro ch hch hmix
    change ancestors? (subclassHeader name c.name :: κ.classes) name = some ch at hch
    rw [hchild] at hch
    cases hch
    obtain ⟨hpos, hneg⟩ := parentDecl.2.2.2.2.2 ns hparent (mixinFreeChain_rootTail c hmix)
    simp only [Cls.rootTail, hkind, Bool.false_eq_true, ite_false] at hpos hneg
    simpa only [hh, List.cons_append, Cls.rootTail, subclassHeader, classHeader,
      Bool.false_eq_true, ite_false] using named_chainSub (name := name) (e := e)
      ready hm.sat htop ho hn ha.live hpos hneg
  · obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := old record hrecord k hk
    exact ⟨hroot, hcls, hmod, hism, fun hk hn => hnew hk (ht.old.newMiss record hrecord hn),
      fun ch hch hmix => hchain ch (ht.old.chain record hrecord ch hch) hmix⟩

theorem ownNames_headerSub (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) :
    ClassOwnNames (subclassHeader name c.name :: κ.classes) h₁ := by
  have hmain := hm.runtime hr
  have ho := hmain.classLive
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hol := lt_size_of_classPayload ho
  apply (ownNames htop hol hn hm.classes hm.ownNames).cons_empty
  intro k hk
  have he := (named_fresh (name := name) (e := e) (p := p) htop ho).symm.trans hk
  have heq := Option.some.inj he
  subst k
  simp only [ownMethods, Heap.classPayload?, get_class (htop ▸ hol), namedObject, freshClassPayload]
  rfl

theorem classChains_headerSub (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some p)
    (hkind : c.isModule = false) (hpl : p < m.heap.objs.size)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : SubclassHeaderFrame κ.classes name c.name) :
    ClassChains (subclassHeader name c.name :: κ.classes) h₁ := by
  have ready := hm.core.classReady
  have hmain := hm.runtime hr
  have ho := hmain.classLive
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have old := classChains (e := e) (p := p) ready hm.sat htop hn hm.classes hm.classChains
  obtain ⟨ns, hparent, hchild⟩ := ht.chain
  intro record hrecord k hk ch hch
  rcases List.mem_cons.mp hrecord with rfl | hrecord
  · change classNamed? _ name = some k at hk
    have he := (named_fresh (name := name) (e := e) (p := p) htop ho).symm.trans hk
    have heq := Option.some.inj he
    subst k
    change ancestors? (subclassHeader name c.name :: κ.classes) name = some ch at hch
    rw [hchild] at hch
    cases hch
    change NamedChain _ (name :: (ns ++ rootAncestors)) _
    apply ordered_chainSub ready hm.sat htop ho hn hpl
    simpa only [Cls.rootTail, hkind, Bool.false_eq_true, ite_false] using
      hm.classChains c hc p hp ns hparent
  · exact old record hrecord k hk ch (ht.old.chain record hrecord ch hch)

end Publish

#print axioms declared_headerSub
#print axioms ownNames_headerSub
#print axioms classChains_headerSub
end Checker.Soundness.FreshClassActual
