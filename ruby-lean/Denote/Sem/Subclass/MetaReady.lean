import Denote.Ty.Ext
import Denote.Sem.Class.BuiltinBases

/-! Heap-only readiness of a retained class's metaclass. Neither a signature nor an
instance ancestor chain establishes these facts; fresh creation publishes them. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def MetaReady (h : Heap) (k : ObjId) : Prop :=
  ∃ e, (h.get k).eigen = some e ∧ (ancestors h e).contains Boot.basicObjectId = true ∧
    ∀ base ch, (base, ch) ∈ builtinBases → e ≠ base

def metaReadyB (h : Heap) (k : ObjId) : Bool :=
  match (h.get k).eigen with
  | none => false
  | some e => (ancestors h e).contains Boot.basicObjectId && builtinBases.all (fun p => e != p.1)

theorem metaReadyB_sound {h : Heap} {k : ObjId} (hb : metaReadyB h k = true) : MetaReady h k := by
  cases he : (h.get k).eigen with
  | none => simp [metaReadyB, he] at hb
  | some e =>
    simp only [metaReadyB, he, Bool.and_eq_true] at hb
    exact ⟨e, he, hb.1, fun base ch hm => bne_iff_ne.mp (List.all_eq_true.mp hb.2 (base, ch) hm)⟩

theorem MetaReady.transport {h h' : Heap} {k : ObjId} (hm : MetaReady h k)
    (he : (h'.get k).eigen = (h.get k).eigen)
    (ha : ∀ e, (h.get k).eigen = some e → ancestors h' e = ancestors h e) : MetaReady h' k := by
  obtain ⟨e, hp, hb, hs⟩ := hm
  exact ⟨e, he.trans hp, (ha e hp).symm ▸ hb, hs⟩

theorem MetaReady.ext {m n : Machine} {k : ObjId} (hm : MetaReady m.heap k)
    (he : Ext m n) (hk : k < m.heap.objs.size) : MetaReady n.heap k :=
  hm.transport (by rw [he.get k hk]) (fun _ _ => he.ancestors _)

theorem MetaReady.methodWrite {h : Heap} {k cls : ObjId} {name : String} {md : MethodDef}
    (hm : MetaReady h k) : MetaReady (defineMethod h cls name md) k :=
  hm.transport (Proof.get_defineMethod_eigen ..) (fun _ _ => Proof.ancestors_defineMethod ..)

theorem MetaReady.ivarOnly {h h' : Heap} {k : ObjId} (hm : MetaReady h k)
    (hi : Proof.IvarOnly h h') : MetaReady h' k :=
  hm.transport (hi.eigen k) (fun e _ => hi.ancestors_eq e)

theorem MetaReady.not_base {h : Heap} {k e base : ObjId} {ch : List String}
    (hm : MetaReady h k) (he : (h.get k).eigen = some e) (hb : (base, ch) ∈ builtinBases) :
    e ≠ base := by
  obtain ⟨e', he', _, hs⟩ := hm
  rw [he] at he'; cases he'
  exact hs base ch hb

#print axioms metaReadyB_sound
#print axioms MetaReady.transport
end Ratchet.Denote
