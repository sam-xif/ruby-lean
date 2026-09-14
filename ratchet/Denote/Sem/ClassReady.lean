import Denote.Ext

/-! Boot facts needed by fresh class creation. Bounded dispatch edges keep old walks
away from newly allocated classes; Object's cached eigenclass prevents old-object mutation.
Neither follows from ancestor-fuel saturation. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure ClassReady (h : Heap) : Prop where
  chains : Proof.ChainsIn h
  objectEigen : ∃ e, (h.get Boot.objectId).eigen = some e

def classReadyB (h : Heap) : Bool :=
  Proof.chainsInB h && (h.get Boot.objectId).eigen.isSome

theorem classReadyB_sound {h : Heap} (hb : classReadyB h = true) : ClassReady h := by
  simp only [classReadyB, Bool.and_eq_true, Option.isSome_iff_exists] at hb
  exact ⟨Proof.chainsInB_sound hb.1, hb.2⟩

theorem ClassReady.ext {m n : Machine} (h : ClassReady m.heap) (he : Ext m n) :
    ClassReady n.heap := by
  refine ⟨he.chains h.chains, ?_⟩
  rw [he.get Boot.objectId h.chains.boot.2.2.2.2]
  exact h.objectEigen

theorem ClassReady.defineMethod {h : Heap} {k : ObjId} {name : String} {md : MethodDef}
    (hc : ClassReady h) : ClassReady (defineMethod h k name md) := by
  refine ⟨Proof.chainsIn_defineMethod hc.chains, ?_⟩
  simpa only [Proof.get_defineMethod_eigen] using hc.objectEigen

theorem ClassReady.ivarOnly {h h' : Heap} (hc : ClassReady h) (hi : Proof.IvarOnly h h') :
    ClassReady h' :=
  ⟨Proof.chainsIn_ivarOnly hi hc.chains, by simpa only [hi.eigen] using hc.objectEigen⟩

#print axioms classReadyB_sound
end Ratchet.Denote
