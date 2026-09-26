import Denote.Sem.Closure.Reify

/-! Native Proc#call resolution is a heap fact, separate from the closure payload.
Overrides, visibility and tombstones must be checked before using the native call proof. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def ProcCallReady (h : Heap) : Prop := ∃ owner, ∃ md : MethodDef,
  Interp.methodOn h Boot.procId "call" = some (owner, md) ∧
  md.builtin = some "Proc#call" ∧ md.undefined = false ∧ md.visibility = .pub ∧
  md.fromPrelude = false ∧
  Interp.crubyShadow h ((ancestors h Boot.procId).takeWhile (· != owner)) "call" = none

def procCallReadyB (h : Heap) : Bool :=
  match Interp.methodOn h Boot.procId "call" with
  | none => false
  | some (owner, md) => md.builtin == some "Proc#call" &&
      !md.undefined && md.visibility == .pub && !md.fromPrelude &&
      (Interp.crubyShadow h ((ancestors h Boot.procId).takeWhile (· != owner)) "call").isNone

theorem procCallReadyB_sound {h : Heap} (hb : procCallReadyB h = true) : ProcCallReady h := by
  cases hl : Interp.methodOn h Boot.procId "call" with
  | none => simp [procCallReadyB, hl] at hb
  | some p =>
    obtain ⟨owner, md⟩ := p
    simp only [procCallReadyB, hl, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      Option.isNone_iff_eq_none] at hb
    obtain ⟨⟨⟨⟨hb, hu⟩, hv⟩, hp⟩, ha⟩ := hb
    exact ⟨owner, md, hl, hb, hu, hv, hp, ha⟩

theorem ProcCallReady.ext {m n : Machine} (h : ProcCallReady m.heap) (he : Ext m n) :
    ProcCallReady n.heap := by
  obtain ⟨owner, md, hl, hb, hu, hv, hp, ha⟩ := h
  refine ⟨owner, md, ?_, hb, hu, hv, hp, ?_⟩
  · simpa only [Interp.methodOn, he.payload, he.ancestors] using hl
  · simpa only [he.ancestors, Interp.crubyShadow, className, he.payload] using ha

/-- Callable dispatch is part of the same guarded conformance as scalar primitives.
Reserving call removes this capability; merely having a Proc payload never grants it. -/
theorem StateOk.procCall {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (h : StateOk κ Γ I m) (hf : nameFreeN κ "call" = true) : ProcCallReady m.heap :=
  dispatch_lookup h.primitiveDispatch (by simp [dispatchMethods]) hf

#print axioms procCallReadyB_sound
#print axioms ProcCallReady.ext
#print axioms StateOk.procCall
end Ratchet.Denote
