import Denote.Sem.Ready
import Denote.Ext
import Denote.Sem.MetaReady

/-! Heap facts needed when an ordinary instance call changes self and lexical scope.
These are obligations to publish with the class, not consequences of a method signature.
Receiver payload is separate: entry binds any value, but dispatch may intercept a Proc. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

private theorem dedup_head (k : ObjId) (xs tail : List ObjId) :
    (xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) (k :: tail)).head? =
      some k := by
  induction xs generalizing tail with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · exact ih tail
    · exact ih (tail ++ [x])

def classFrontB (h : Heap) (k : ObjId) : Bool :=
  (h.classPayload? k).any (fun cp => cp.prepends.isEmpty)

theorem classFrontB_sound {h : Heap} {k : ObjId} (hf : classFrontB h k = true) :
    ∃ rest, ancestors h k = k :: rest := by
  cases hp : h.classPayload? k with
  | none => simp [classFrontB, hp] at hf
  | some cp =>
    have hn : cp.prepends = [] := by simpa [classFrontB, hp] using hf
    have hh : (ancestors h k).head? = some k := by
      simp only [ancestors, ancestors.go, hp, hn, List.reverse_nil, List.flatMap_nil,
        List.nil_append, List.cons_append, List.foldl_cons, List.contains_nil,
        Bool.false_eq_true, ↓reduceIte, List.nil_append]
      exact dedup_head k _ []
    cases ha : ancestors h k with
    | nil => simp [ha] at hh
    | cons a rest =>
      have hk : a = k := by simpa only [ha, List.head?_cons, Option.some.injEq] using hh
      exact ⟨rest, by simpa only [hk] using ha⟩

def instanceConstResolve (h : Heap) (k : ObjId) (n : String) : Option Value :=
  ([k, Boot.objectId].firstM (fun j => constOwn h j n)).orElse
    (fun _ => constLookupFrom h k n)

/-- The finite names whose absence is stronger than MethodsExact's prelude allowance. -/
def shadowableNames : List String := ["lambda", "proc", "x"]

def NamesAt (free : String → Bool) (h : Heap) (k : ObjId) : Prop :=
  ∀ n ∈ shadowableNames, ∀ owner md, Interp.methodOn h k n = some (owner, md) →
    md.builtin.isSome = true ∨ md.undefined = true ∨ free n = false

def namesAtB (free : String → Bool) (h : Heap) (k : ObjId) : Bool :=
  shadowableNames.all fun n => (Interp.methodOn h k n).all fun (_, md) =>
    md.builtin.isSome || md.undefined || !free n

theorem namesAtB_sound {free : String → Bool} {h : Heap} {k : ObjId}
    (hp : namesAtB free h k = true) : NamesAt free h k := by
  intro n hn owner md hm
  have hh := List.all_eq_true.mp hp n hn
  simpa only [hm, Option.all_some, Bool.or_eq_true, Bool.not_eq_true', or_assoc] using hh

theorem NamesAt.recontext {free free' : String → Bool} {h : Heap} {k : ObjId}
    (hp : NamesAt free h k) (hn : ∀ n, free n = false → free' n = false) : NamesAt free' h k :=
  fun n hm owner md hl => (hp n hm owner md hl).imp id (Or.imp id (hn n))

structure InstanceSiteAt (free : String → Bool) (cn : String) (k : ObjId) (h : Heap) : Prop where
  named : classNamed? h cn = some k
  front : classFrontB h k = true
  hook : definitionHookQuietB h k = true
  constants : ∀ n, instanceConstResolve h k n = constLookup h n
  names : NamesAt free h k
  metaclass : MetaReady h k
  /-- Retain class-object dispatch separately: subclass-body self inherits this chain,
  not the instance chain. Prelude code alone is not an absence proof. -/
  classNames : NamesAt free h (classOf h (.ref k))

/-- Only negative-name information affects a site's meaning, not the caller's scope. -/
abbrev InstanceSite (κ : Ctx) := InstanceSiteAt (nameFreeN κ)

/-- A class payload pins its reference live, even though Heap.get is total. -/
theorem lt_size_of_classPayload {h : Heap} {o : ObjId}
    (hp : (h.classPayload? o).isSome = true) : o < h.objs.size := by
  by_cases hk : o < h.objs.size
  · exact hk
  · exfalso
    simp only [Heap.classPayload?, Heap.get, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using hk), Option.getD_none] at hp
    exact absurd hp (by decide)

theorem InstanceSite.live {κ : Ctx} {cn : String} {k : ObjId} {h : Heap}
    (site : InstanceSite κ cn k h) : k < h.objs.size := by
  have hn := site.named
  unfold classNamed? at hn
  split at hn
  · split at hn
    · rename_i hp; cases hn; exact lt_size_of_classPayload hp
    · cases hn
  · cases hn

theorem InstanceSite.recontext {κ κ' : Ctx} {cn : String} {k : ObjId} {h : Heap}
    (site : InstanceSite κ cn k h)
    (hn : ∀ n, nameFreeN κ n = false → nameFreeN κ' n = false) : InstanceSite κ' cn k h := by
  exact ⟨site.named, site.front, site.hook, site.constants, site.names.recontext hn,
    site.metaclass, site.classNames.recontext hn⟩

/-- Scope-independent, so the same site survives a frame change or an allocation.
This does not claim that method installation or class mutation preserves it. -/
theorem InstanceSite.ext {κ : Ctx} {cn : String} {k : ObjId} {m n : Machine}
    (h : InstanceSite κ cn k m.heap) (he : Ext m n)
    (hl : k < m.heap.objs.size) : InstanceSite κ cn k n.heap := by
  have hm (j : ObjId) (mn : String) : Interp.methodOn n.heap j mn =
      Interp.methodOn m.heap j mn := by simp only [Interp.methodOn, he.payload, he.ancestors]
  have hc (j : ObjId) (name : String) : constOwn n.heap j name = constOwn m.heap j name := by
    simp only [constOwn, he.payload]
  have hi (name : String) : constLookupFrom n.heap k name = constLookupFrom m.heap k name := by
    simp only [constLookupFrom, he.payload, he.ancestors]
  have hlk : lookup n.heap (.ref k) "method_added" = lookup m.heap (.ref k) "method_added" := by
    have hg (ks : List ObjId) : lookup.go n.heap "method_added" ks =
        lookup.go m.heap "method_added" ks := by
      induction ks with
      | nil => rfl
      | cons j ks ih => simp only [lookup.go, he.payload, ih]
    simp only [lookup, classOf, he.get k hl, he.ancestors, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, h.metaclass.ext he hl, ?_⟩
  · simpa only [he.classNamed?_eq] using h.named
  · simpa only [classFrontB, he.payload] using h.front
  · simpa only [definitionHookQuietB, hlk] using h.hook
  · intro name
    simpa only [instanceConstResolve, hc, hi, he.constLookup_eq] using h.constants name
  · intro name hn owner md hmd
    rw [hm] at hmd
    exact h.names name hn owner md hmd
  · intro name hn owner md hmd
    rw [show classOf n.heap (.ref k) = classOf m.heap (.ref k) from by
      simp only [classOf, he.get k hl], hm] at hmd
    exact h.classNames name hn owner md hmd

/-- Installed classes persist after leaving a scope. The pending lexical class requests
its site before a method/constructor record has been published. No new Ctx field is needed. -/
def classSiteNames (κ : Ctx) : List String :=
  κ.classes.map (·.name) ++ κ.scope.runtimeClass.toList

def ClassSitesOk (κ : Ctx) (h : Heap) : Prop :=
  ∀ cn ∈ classSiteNames κ, ∃ k, InstanceSite κ cn k h

theorem ClassSitesOk.of_class {κ : Ctx} {h : Heap} (sites : ClassSitesOk κ h)
    {c : Cls} (hc : c ∈ κ.classes) : ∃ k, InstanceSite κ c.name k h :=
  sites c.name (List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

theorem ClassSitesOk.of_scope {κ : Ctx} {h : Heap} (sites : ClassSitesOk κ h)
    {cn : String} (hc : κ.scope.runtimeClass = some cn) : ∃ k, InstanceSite κ cn k h :=
  sites cn (by simp [classSiteNames, hc])

theorem ClassSitesOk.at_class {κ : Ctx} {h : Heap} (sites : ClassSitesOk κ h)
    {c : Cls} {k : ObjId} (hc : c ∈ κ.classes) (hn : classNamed? h c.name = some k) :
    InstanceSite κ c.name k h := by
  obtain ⟨k', site⟩ := sites.of_class hc
  have he : k' = k := Option.some.inj (site.named.symm.trans hn)
  subst k'
  exact site

theorem ClassSitesOk.metaclass {κ : Ctx} {h : Heap} (sites : ClassSitesOk κ h)
    {c : Cls} {k : ObjId} (hc : c ∈ κ.classes) (hn : classNamed? h c.name = some k) :
    MetaReady h k := (sites.at_class hc hn).metaclass

theorem ClassSitesOk.recontext {κ κ' : Ctx} {h : Heap} (sites : ClassSitesOk κ h)
    (hc : ∀ cn ∈ classSiteNames κ', cn ∈ classSiteNames κ)
    (hn : ∀ n, nameFreeN κ n = false → nameFreeN κ' n = false) : ClassSitesOk κ' h := by
  intro cn hcn
  obtain ⟨k, site⟩ := sites cn (hc cn hcn)
  exact ⟨k, site.recontext hn⟩

theorem ClassSitesOk.ext {κ : Ctx} {m n : Machine} (sites : ClassSitesOk κ m.heap)
    (he : Ext m n) : ClassSitesOk κ n.heap := by
  intro cn hcn
  obtain ⟨k, site⟩ := sites cn hcn
  exact ⟨k, site.ext he site.live⟩

#print axioms classFrontB_sound
#print axioms namesAtB_sound
#print axioms InstanceSite.ext
end Ratchet.Denote
