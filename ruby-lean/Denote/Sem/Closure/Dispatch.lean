import Denote.Sem.Closure.Reify

/-! Native Proc#call resolution is a heap fact, separate from the closure payload.
Overrides, visibility and tombstones must be checked before using the native call proof. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def ProcCallReady (h : Heap) : Prop := ∃ md : MethodDef,
  Interp.methodOn h Boot.procId "call" = some (Boot.procId, md) ∧
  md.builtin = some "Proc#call" ∧ md.undefined = false ∧ md.visibility = .pub ∧
  md.fromPrelude = false ∧ (ancestors h Boot.procId).takeWhile (· != Boot.procId) = []

def procCallReadyB (h : Heap) : Bool :=
  match Interp.methodOn h Boot.procId "call" with
  | none => false
  | some (owner, md) => owner == Boot.procId && md.builtin == some "Proc#call" &&
      !md.undefined && md.visibility == .pub && !md.fromPrelude &&
      ((ancestors h Boot.procId).takeWhile (· != Boot.procId)).isEmpty

theorem procCallReadyB_sound {h : Heap} (hb : procCallReadyB h = true) : ProcCallReady h := by
  cases hl : Interp.methodOn h Boot.procId "call" with
  | none => simp [procCallReadyB, hl] at hb
  | some p =>
    obtain ⟨owner, md⟩ := p
    simp only [procCallReadyB, hl, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      List.isEmpty_iff] at hb
    obtain ⟨⟨⟨⟨⟨rfl, hb⟩, hu⟩, hv⟩, hp⟩, ha⟩ := hb
    exact ⟨md, hl, hb, hu, hv, hp, ha⟩

theorem ProcCallReady.ext {m n : Machine} (h : ProcCallReady m.heap) (he : Ext m n) :
    ProcCallReady n.heap := by
  obtain ⟨md, hl, hb, hu, hv, hp, ha⟩ := h
  refine ⟨md, ?_, hb, hu, hv, hp, ?_⟩
  · simpa only [Interp.methodOn, he.payload, he.ancestors] using hl
  · simpa only [he.ancestors] using ha

#print axioms procCallReadyB_sound
#print axioms ProcCallReady.ext
end Ratchet.Denote
