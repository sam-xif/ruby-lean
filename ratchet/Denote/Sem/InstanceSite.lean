import Denote.Sem.State

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

structure InstanceSite (κ : Ctx) (cn : String) (k : ObjId) (h : Heap) : Prop where
  named : classNamed? h cn = some k
  front : classFrontB h k = true
  hook : definitionHookQuietB h k = true
  constants : ∀ n, instanceConstResolve h k n = constLookup h n
  names : ∀ n ∈ shadowableNames, ∀ owner md,
    Interp.methodOn h k n = some (owner, md) →
      md.builtin.isSome = true ∨ md.undefined = true ∨ nameFreeN κ n = false

theorem InstanceSite.constScope {κ : Ctx} {cn : String} {k : ObjId} {m : Machine}
    (h : InstanceSite κ cn k m.heap) (hc : m.currentFrame.cref = [k, Boot.objectId])
    (ho : m.currentFrame.defmod = k) : ConstScopeOk m := by
  intro n
  simpa only [constResolveAt, hc, ho, instanceConstResolve] using h.constants n

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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [he.classNamed?_eq] using h.named
  · simpa only [classFrontB, he.payload] using h.front
  · simpa only [definitionHookQuietB, lookup_eq_methodOn, classOf, he.get k hl, hm] using h.hook
  · intro name
    simpa only [instanceConstResolve, hc, hi, he.constLookup_eq] using h.constants name
  · intro name hn owner md hmd
    rw [hm] at hmd
    exact h.names name hn owner md hmd

#print axioms classFrontB_sound
#print axioms InstanceSite.ext
end Ratchet.Denote
