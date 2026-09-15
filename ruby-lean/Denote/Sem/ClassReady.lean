import Denote.Sem.ConstLive
import Denote.Sem.BuiltinBases

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
  /-- Object's eigenclass is not a builtin value base, even if its queries look compatible. -/
  eigenSeparate : ∀ e, (h.get Boot.objectId).eigen = some e →
    ∀ base ch, (base, ch) ∈ builtinBases → e ≠ base
  constRefs : ConstRefsLive h
  /-- A fresh class inherits Object itself, not necessarily main's dispatch class. -/
  objectChain : ancestors h Boot.objectId = [Boot.objectId, Boot.kernelId, Boot.basicObjectId]

def eigenSeparateB (h : Heap) : Bool :=
  match (h.get Boot.objectId).eigen with
  | none => false
  | some e => builtinBases.all (fun p => e != p.1)

theorem eigenSeparateB_sound {h : Heap} (hb : eigenSeparateB h = true)
    {e : ObjId} (he : (h.get Boot.objectId).eigen = some e)
    {base : ObjId} {ch : List String} (hbase : (base, ch) ∈ builtinBases) : e ≠ base := by
  simp only [eigenSeparateB, he] at hb
  exact bne_iff_ne.mp (List.all_eq_true.mp hb (base, ch) hbase)

def classReadyB (h : Heap) : Bool :=
  Proof.chainsInB h &&
    (match (h.get Boot.objectId).eigen with
     | some e => (ancestors h e).contains Boot.basicObjectId
     | none => false) &&
    (ancestors h Boot.classId).contains Boot.basicObjectId && eigenSeparateB h && constRefsLiveB h &&
    (ancestors h Boot.objectId == [Boot.objectId, Boot.kernelId, Boot.basicObjectId])

theorem classReadyB_sound {h : Heap} (hb : classReadyB h = true) : ClassReady h := by
  simp only [classReadyB, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨hch, hei⟩, hclass⟩, hsep⟩, href⟩, hroot⟩ := hb
  refine ⟨Proof.chainsInB_sound hch, ?_, hclass,
    fun _ he _ _ hbase => eigenSeparateB_sound hsep he hbase, constRefsLiveB_sound href,
    beq_iff_eq.mp hroot⟩
  cases he : (h.get Boot.objectId).eigen with
  | none => simp only [he] at hei; cases hei
  | some e => exact ⟨e, rfl, by simpa only [he] using hei⟩

theorem ClassReady.ext {m n : Machine} (h : ClassReady m.heap) (he : Ext m n) :
    ClassReady n.heap := by
  refine ⟨he.chains h.chains, ?_, ?_, ?_, h.constRefs.ext he, ?_⟩
  · simpa only [he.get Boot.objectId h.chains.boot.2.2.2.2, he.ancestors] using h.objectEigen
  · simpa only [he.ancestors] using h.classBasic
  · simpa only [he.get Boot.objectId h.chains.boot.2.2.2.2] using h.eigenSeparate
  · simpa only [he.ancestors] using h.objectChain

theorem ClassReady.defineMethod {h : Heap} {k : ObjId} {name : String} {md : MethodDef}
    (hc : ClassReady h) : ClassReady (defineMethod h k name md) := by
  refine ⟨Proof.chainsIn_defineMethod hc.chains, ?_, ?_, ?_, hc.constRefs.defineMethod, ?_⟩
  · simpa only [Proof.get_defineMethod_eigen, Proof.ancestors_defineMethod] using hc.objectEigen
  · simpa only [Proof.ancestors_defineMethod] using hc.classBasic
  · simpa only [Proof.get_defineMethod_eigen] using hc.eigenSeparate
  · simpa only [Proof.ancestors_defineMethod] using hc.objectChain

theorem ClassReady.ivarOnly {h h' : Heap} (hc : ClassReady h) (hi : Proof.IvarOnly h h') :
    ClassReady h' :=
  ⟨Proof.chainsIn_ivarOnly hi hc.chains,
    by simpa only [hi.eigen, hi.ancestors_eq] using hc.objectEigen,
    by simpa only [hi.ancestors_eq] using hc.classBasic,
    by simpa only [hi.eigen] using hc.eigenSeparate, hc.constRefs.ivarOnly hi,
    by simpa only [hi.ancestors_eq] using hc.objectChain⟩

#print axioms classReadyB_sound
end Ratchet.Denote
