import Denote.Sem.Names.ConstLive

/-! A named capability for plain-object allocation. Unlike a fresh class's exact root
chain, this admits ordinary inheritance. It says nothing about initializer code or safety. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure PlainAllocator (h : Heap) (k : ObjId) : Prop where
  live : k < h.objs.size
  notClass : k ≠ Boot.classId
  notModule : k ≠ Boot.moduleId
  notMath : k ≠ Boot.mathId
  notString : k ≠ Boot.stringId
  module : (h.classPayload? k).map (·.isModule) = some false
  rooted : (ancestors h k).contains Boot.basicObjectId = true
  noCore : Builtins.allocatableCore h k = none
  noPayload : (ancestors h k).any
    (fun a => Builtins.payloadCoreClasses.contains a || a == Boot.exceptionId) = false

theorem PlainAllocator.payload {h : Heap} {k : ObjId} (hc : PlainAllocator h k) :
    ∃ cp, (h.get k).payload = .cls cp ∧ cp.isModule = false := by
  have hm := hc.module
  unfold Heap.classPayload? at hm
  cases hp : (h.get k).payload <;> simp_all

theorem PlainAllocator.transport {h h' : Heap} {k : ObjId} (hc : PlainAllocator h k)
    (hl : h.objs.size ≤ h'.objs.size)
    (hp : (h'.classPayload? k).map (·.isModule) = (h.classPayload? k).map (·.isModule))
    (ha : ancestors h' k = ancestors h k) : PlainAllocator h' k :=
  ⟨Nat.lt_of_lt_of_le hc.live hl, hc.notClass, hc.notModule, hc.notMath, hc.notString,
    hp.trans hc.module, ha ▸ hc.rooted,
    by simpa only [Builtins.allocatableCore, ha] using hc.noCore, ha ▸ hc.noPayload⟩

def AllocatorsOk (names : List String) (h : Heap) : Prop :=
  ∀ cn ∈ names, ∃ k, classNamed? h cn = some k ∧ PlainAllocator h k

theorem AllocatorsOk.ext {names : List String} {m n : Machine}
    (hc : AllocatorsOk names m.heap) (he : Ext m n) : AllocatorsOk names n.heap := by
  intro cn hn
  obtain ⟨k, hk, hp⟩ := hc cn hn
  exact ⟨k, by rw [he.classNamed?_eq]; exact hk,
    hp.transport he.size (by rw [he.payload]) (he.ancestors k)⟩

theorem AllocatorsOk.defineMethod {names : List String} {h : Heap} {cls : ObjId}
    {name : String} {md : MethodDef} (hc : AllocatorsOk names h) :
    AllocatorsOk names (defineMethod h cls name md) := by
  intro cn hn
  obtain ⟨k, hk, hp⟩ := hc cn hn
  refine ⟨k, ?_, hp.transport (by rw [Proof.objs_size_defineMethod]; exact Nat.le_refl _) ?_
    (Proof.ancestors_defineMethod ..)⟩
  · have hl (g : Heap) : constLookup g cn = constOwn g Boot.objectId cn := by
      cases cp : g.classPayload? Boot.objectId <;> simp [constLookup, constOwn, cp]
    simpa only [classNamed?, hl, Proof.constOwn_defineMethod,
      Proof.classPayload?_isSome_defineMethod] using hk
  · have he := congrArg (Option.map Prod.snd) (Proof.clsName_defineMethod h cls k name md)
    simpa only [Option.map_map, Function.comp_def] using he

theorem AllocatorsOk.ivarOnly {names : List String} {h h' : Heap}
    (hc : AllocatorsOk names h) (hi : Proof.IvarOnly h h') : AllocatorsOk names h' := by
  intro cn hn
  obtain ⟨k, hk, hp⟩ := hc cn hn
  exact ⟨k, by simpa only [classNamed?, constLookup, hi.classPayload] using hk,
    hp.transport (by rw [hi.size]; exact Nat.le_refl _) (by rw [hi.classPayload]) (hi.ancestors_eq k)⟩

#print axioms AllocatorsOk.ext
#print axioms AllocatorsOk.defineMethod
end Ratchet.Denote
