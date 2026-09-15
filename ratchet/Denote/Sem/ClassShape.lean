import Denote.Sem.ClassHeap

/-! Physical allocation facts of a fresh ordinary class. These are distinct from its
method signatures and from the names the declaration table assigns to its ancestors. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

structure OrdinaryClass (h : Heap) (k : ObjId) : Prop where
  live : k < h.objs.size
  notClass : k ≠ Boot.classId
  notModule : k ≠ Boot.moduleId
  module : (h.classPayload? k).map (·.isModule) = some false
  chain : ancestors h k = [k, Boot.objectId, Boot.kernelId, Boot.basicObjectId]
  noCore : Builtins.allocatableCore h k = none
  noPayload : (ancestors h k).any
    (fun a => Builtins.payloadCoreClasses.contains a || a == Boot.exceptionId) = false

theorem OrdinaryClass.payload {h : Heap} {k : ObjId} (hc : OrdinaryClass h k) :
    ∃ cp, (h.get k).payload = .cls cp ∧ cp.isModule = false := by
  have hm := hc.module
  unfold Heap.classPayload? at hm
  cases hp : (h.get k).payload <;> simp_all

theorem OrdinaryClass.rooted {h : Heap} {k : ObjId} (hc : OrdinaryClass h k) :
    (ancestors h k).contains Boot.basicObjectId = true := by simp [hc.chain]

theorem OrdinaryClass.plain {h : Heap} {k : ObjId} (hc : OrdinaryClass h k)
    (hm : k ≠ Boot.mathId) : PlainAllocator h k := by
  refine ⟨hc.live, hc.notClass, hc.notModule, hm, ?_, hc.module, hc.rooted, hc.noCore, hc.noPayload⟩
  intro he
  have hn := hc.noPayload
  rw [hc.chain] at hn
  simp [he, Builtins.payloadCoreClasses] at hn

theorem FreshClass.ordinary {h : Heap} {d : ObjId} {name q : String} {e : ObjId}
    (hc : ClassReady h) (hs : Proof.Saturated h) :
    OrdinaryClass (freshClsHeap h d name q e) h.objs.size := by
  have hchain : ancestors (freshClsHeap h d name q e) h.objs.size =
      [h.objs.size, Boot.objectId, Boot.kernelId, Boot.basicObjectId] := by
    rw [Proof.Judgment.ancestors_freshC_k hc.chains hs, hc.objectChain]
  have hne (k : ObjId) (hk : k ≤ Boot.procId) : h.objs.size ≠ k :=
    (Nat.ne_of_lt (Nat.lt_of_le_of_lt hk hc.chains.boot.2.2.2.1)).symm
  refine ⟨?_, hne _ (by decide), hne _ (by decide), ?_, hchain, ?_, ?_⟩
  · rw [Proof.Judgment.freshClsHeap_size]
    exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  · rw [Proof.Judgment.freshClsHeap_cp_k]; rfl
  · simp [Builtins.allocatableCore, hchain,
      Boot.objectId, Boot.kernelId, Boot.basicObjectId, Boot.stringId, Boot.arrayId,
      Boot.hashId, Boot.exceptionId]
    exact ⟨⟨⟨hne _ (by decide), hne _ (by decide)⟩, hne _ (by decide)⟩, hne _ (by decide)⟩
  · simp [Builtins.payloadCoreClasses, hchain,
      Boot.objectId, Boot.kernelId, Boot.basicObjectId, Boot.stringId, Boot.arrayId,
      Boot.hashId, Boot.procId, Boot.integerId, Boot.floatId, Boot.symbolId, Boot.exceptionId]
    exact ⟨⟨hne _ (by decide), hne _ (by decide), hne _ (by decide), hne _ (by decide),
      hne _ (by decide), hne _ (by decide), hne _ (by decide)⟩, hne _ (by decide)⟩

#print axioms FreshClass.ordinary
end Ratchet.Denote
