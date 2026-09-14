import Denote.Ext

/-! Boot facts needed by fresh class creation. Bounded dispatch edges keep old walks
away from newly allocated classes; Object's cached eigenclass prevents old-object mutation.
Both new objects must remain BasicObjects to preserve types at formerly dangling references.
These facts do not follow from ancestor-fuel saturation. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure ClassReady (h : Heap) : Prop where
  chains : Proof.ChainsIn h
  objectEigen : ∃ e, (h.get Boot.objectId).eigen = some e ∧
    (ancestors h e).contains Boot.basicObjectId = true
  classBasic : (ancestors h Boot.classId).contains Boot.basicObjectId = true

def classReadyB (h : Heap) : Bool :=
  Proof.chainsInB h &&
    (match (h.get Boot.objectId).eigen with
     | some e => (ancestors h e).contains Boot.basicObjectId
     | none => false) &&
    (ancestors h Boot.classId).contains Boot.basicObjectId

theorem classReadyB_sound {h : Heap} (hb : classReadyB h = true) : ClassReady h := by
  simp only [classReadyB, Bool.and_eq_true] at hb
  refine ⟨Proof.chainsInB_sound hb.1.1, ?_, hb.2⟩
  cases he : (h.get Boot.objectId).eigen with
  | none => simp only [he] at hb; cases hb.1.2
  | some e => exact ⟨e, rfl, by simpa only [he] using hb.1.2⟩

theorem ClassReady.ext {m n : Machine} (h : ClassReady m.heap) (he : Ext m n) :
    ClassReady n.heap := by
  refine ⟨he.chains h.chains, ?_, ?_⟩
  · simpa only [he.get Boot.objectId h.chains.boot.2.2.2.2, he.ancestors] using h.objectEigen
  · simpa only [he.ancestors] using h.classBasic

theorem ClassReady.defineMethod {h : Heap} {k : ObjId} {name : String} {md : MethodDef}
    (hc : ClassReady h) : ClassReady (defineMethod h k name md) := by
  refine ⟨Proof.chainsIn_defineMethod hc.chains, ?_, ?_⟩
  · simpa only [Proof.get_defineMethod_eigen, Proof.ancestors_defineMethod] using hc.objectEigen
  · simpa only [Proof.ancestors_defineMethod] using hc.classBasic

theorem ClassReady.ivarOnly {h h' : Heap} (hc : ClassReady h) (hi : Proof.IvarOnly h h') :
    ClassReady h' :=
  ⟨Proof.chainsIn_ivarOnly hi hc.chains,
    by simpa only [hi.eigen, hi.ancestors_eq] using hc.objectEigen,
    by simpa only [hi.ancestors_eq] using hc.classBasic⟩

#print axioms classReadyB_sound
end Ratchet.Denote
