import Denote.Sem.Closure.Reify
import Ratchet.Guards.ClosureFlow

/-! Native Proc#call resolution is a heap fact, separate from the closure payload.
Overrides, visibility and tombstones must be checked before using the native call proof. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def ProcDispatchReady (h : Heap) (name : String) : Prop := ∃ owner, ∃ md : MethodDef,
  Interp.methodOn h Boot.procId name = some (owner, md) ∧
  md.builtin = some ("Proc#" ++ name) ∧ md.undefined = false ∧ md.visibility = .pub ∧
  md.fromPrelude = false ∧
  Interp.crubyShadow h ((ancestors h Boot.procId).takeWhile (· != owner)) name = none

abbrev ProcCallReady (h : Heap) : Prop := ProcDispatchReady h "call"

def procDispatchReadyB (h : Heap) (name : String) : Bool :=
  match Interp.methodOn h Boot.procId name with
  | none => false
  | some (owner, md) => md.builtin == some ("Proc#" ++ name) &&
      !md.undefined && md.visibility == .pub && !md.fromPrelude &&
      (Interp.crubyShadow h ((ancestors h Boot.procId).takeWhile (· != owner)) name).isNone

abbrev procCallReadyB (h : Heap) : Bool := procDispatchReadyB h "call"

theorem procDispatchReadyB_sound {h : Heap} {name : String}
    (hb : procDispatchReadyB h name = true) : ProcDispatchReady h name := by
  cases hl : Interp.methodOn h Boot.procId name with
  | none => simp [procDispatchReadyB, hl] at hb
  | some p =>
    obtain ⟨owner, md⟩ := p
    simp only [procDispatchReadyB, hl, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      Option.isNone_iff_eq_none] at hb
    obtain ⟨⟨⟨⟨hb, hu⟩, hv⟩, hp⟩, ha⟩ := hb
    exact ⟨owner, md, hl, hb, hu, hv, hp, ha⟩

theorem procCallReadyB_sound {h : Heap} (hb : procCallReadyB h = true) : ProcCallReady h :=
  procDispatchReadyB_sound hb

theorem ProcDispatchReady.ext {m n : Machine} {name : String}
    (h : ProcDispatchReady m.heap name) (he : Ext m n)
    (hn : Proof.NamesOk m.heap) (hc : Proof.ChainsIn m.heap) : ProcDispatchReady n.heap name := by
  obtain ⟨owner, md, hl, hb, hu, hv, hp, ha⟩ := h
  refine ⟨owner, md, ?_, hb, hu, hv, hp, ?_⟩
  · simpa only [he.methodOn_eq hc] using hl
  · simpa only [he.ancestors, he.crubyShadow_eq hn] using ha

theorem ProcCallReady.ext {m n : Machine} (h : ProcCallReady m.heap) (he : Ext m n) :
    Proof.NamesOk m.heap → Proof.ChainsIn m.heap → ProcCallReady n.heap :=
  ProcDispatchReady.ext h he

theorem StateOk.procDispatch {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {name : String}
    (h : StateOk κ Γ I m) (hf : nameFreeN κ name = true) (hn : procCallNameB name = true) :
    ProcDispatchReady m.heap name := by
  have hn' : name = "call" ∨ name = "[]" := by simpa [procCallNameB] using hn
  apply dispatch_lookup h.primitiveDispatch ?_ hf
  rcases hn' with rfl | rfl <;> simp [dispatchMethods]

/-- Callable dispatch is part of the same guarded conformance as scalar primitives.
Reserving call removes this capability; merely having a Proc payload never grants it. -/
theorem StateOk.procCall {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (h : StateOk κ Γ I m) (hf : nameFreeN κ "call" = true) : ProcCallReady m.heap :=
  dispatch_lookup h.primitiveDispatch (by simp [dispatchMethods]) hf

#print axioms procCallReadyB_sound
#print axioms ProcCallReady.ext
#print axioms StateOk.procCall
#print axioms StateOk.procDispatch
end Ratchet.Denote
