import Books.TypeSoundness.Conformance.Class.ClassChainsActual
import Books.TypeSoundness.Conformance.Class.ClassDeclaredActual
import Books.TypeSoundness.Conformance.Class.ClassQueriesActual
import Books.TypeSoundness.Conformance.Class.ClassNew
import Books.TypeSoundness.Checker.Guards.ClassHeader
import Books.TypeSoundness.Conformance.Names.NativeGuards

/-! Repair the original fresh-header publication on the actual named/attached heap. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e

theorem named_fresh_only (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size) (hl : ConstRefsLive m.heap) {cn : String}
    (hk : classNamed? h₁ cn = some m.heap.objs.size) : cn = name := by
  by_cases hn : cn = name
  · exact hn
  have href := classNamed_constOwn hk
  rw [constOwn_other htop ho ho hn] at href
  exact False.elim ((Nat.lt_irrefl _) (hl cn _ href))

theorem new_dispatch (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hel : e < m.heap.objs.size)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hne : name.isEmpty = false)
    (hq : classNativeQuietB name "new" = true) (hlmain : Boot.mainId < m.heap.objs.size)
    (hD : NewDispatch m.heap (classOf m.heap (.ref Boot.objectId))) :
    NewDispatch h₁ (classOf h₁ (.ref m.heap.objs.size)) := by
  obtain ⟨hn₁, hn₂⟩ := classNativeQuietB_sound hq
  have hm (mn : String) : Interp.methodOn h₁ (classOf h₁ (.ref m.heap.objs.size)) mn =
      Interp.methodOn m.heap (classOf m.heap (.ref Boot.objectId)) mn := by
    rw [classOf_class hd, method_eigen hc hs hd hel]
    simp only [classOf, he]
  refine ⟨?_, by simpa only [hm] using hD.present⟩
  intro owner md hl
  obtain ⟨hb, hu, hv, hp, hsh⟩ := hD.found owner md ((hm "new").symm ▸ hl)
  refine ⟨hb, hu, hv, hp, ?_⟩
  rw [classOf_class hd]
  apply shadow_before_source hnames hc hs hd hel hne hn₁ hn₂ (classNativeQuietB_singleton hq) hlmain
    hc.boot.2.2.2.2
  simpa only [source, Subclass.source, if_neg (Nat.succ_ne_self _), ite_true, classOf, he] using hsh

theorem named_chain (hc : ClassReady m.heap) (hs : Saturated m.heap) (hr : RootNames m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) :
    (∀ cn ∈ name :: rootAncestors, ∃ k, classNamed? h₁ cn = some k ∧
      (ancestors h₁ m.heap.objs.size).contains k = true) ∧
    (∀ cn k, classNamed? h₁ cn = some k → (ancestors h₁ m.heap.objs.size).contains k = true →
      cn ∈ name :: rootAncestors) := by
  have hol := lt_size_of_classPayload ho
  have hchain := ordinary_chain (name := name) (e := e) hc hs (htop ▸ hol)
  have roots := rootNames (e := e) (p := Boot.objectId) hr hc.constRefs htop ho hn
  constructor
  · intro cn hcn
    rcases List.mem_cons.mp hcn with rfl | hcn
    · exact ⟨_, named_fresh htop ho, by simp [hchain]⟩
    · have hm : cn ∈ rootNameIds.map (·.1) := hcn
      obtain ⟨⟨cn', k⟩, hrow, rfl⟩ := List.mem_map.mp hm
      have hk : k ∈ rootIds := by
        change k ∈ rootNameIds.map (·.2)
        exact List.mem_map.mpr ⟨(cn', k), hrow, rfl⟩
      refine ⟨k, roots.named cn' k hrow, ?_⟩
      rw [hchain]
      exact List.contains_iff_mem.mpr (List.mem_cons_of_mem _ hk)
  · intro cn k hk hanc
    rw [hchain] at hanc
    rcases List.mem_cons.mp (List.contains_iff_mem.mp hanc) with he | hm
    · subst k
      rw [named_fresh_only htop hol hc.constRefs hk]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (roots.only cn k hk hm)

variable {κ : Ctx} {n : Machine}

theorem declared_header (hnames : NamesOk m.heap) (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hr : RootNames m.heap) (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hlmain : Boot.mainId < m.heap.objs.size)
    (hq : classNativeQuietB name "new" = true) (hf : objectClassFlagsB m.heap = true)
    (hD : NewDispatch m.heap (classOf m.heap (.ref Boot.objectId)))
    (hh : n.heap = h₁) (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m)
    (ht : HeaderTableFrame κ.classes name) : DeclClassOk (classHeaderCtx κ name) n := by
  have hol := lt_size_of_classPayload ho
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hol
  have old := declared hnames hc.chains hs htop ho hn hh hclasses hp
  intro c hmem k hk
  change c ∈ classHeader name :: κ.classes at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · change classNamed? n.heap name = some k at hk
    rw [hh, named_fresh htop ho] at hk
    cases hk
    have shape := plain (name := name) (e := e) hc hs hd hf
    have dispatch := new_dispatch hnames hc.chains hs hd (hc.chains.eigen _ hol _ he) he hne hq hlmain hD
    have chain := named_chain (e := e) hc hs hr htop ho hn
    rw [← hh] at shape dispatch chain
    refine ⟨fun _ => shape.rooted, shape.notClass, shape.notModule, shape.module,
      fun _ _ => ⟨dispatch.found, dispatch.present⟩, ?_⟩
    intro ch hch _
    change ancestors? (classHeader name :: κ.classes) name = some ch at hch
    rw [classHeader_ancestors] at hch
    cases hch
    exact chain
  · obtain ⟨hroot, hcls, hmod, hism, hnew, hchain⟩ := old c hmem k hk
    exact ⟨hroot, hcls, hmod, hism, fun hk hn => hnew hk (ht.newMiss c hmem hn),
      fun ch hch hmix => hchain ch (ht.chain c hmem ch hch) hmix⟩

#print axioms new_dispatch
#print axioms named_chain
#print axioms declared_header
end Checker.Soundness.FreshClassActual
