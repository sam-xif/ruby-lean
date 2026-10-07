import Checker.Guards.RootInit
import Books.TypeSoundness.Denotation.Ext
import RubyCore.Interp.Dispatch

/-! Root initialization is a heap contract indexed by the existing top-level def table.
It admits declared Object#initialize but never infers a body proof from its signature. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

/-- Proof-side classifier retained after constructor entry moved to queued
    ordinary dispatch. It records whether a user initializer exists; it is not
    an executable constructor shortcut. -/
def userInit? (h : Heap) (k : ObjId) : Option MethodDef :=
  match Interp.methodOn h k "initialize" with
  | some (_, md) => if md.builtin.isNone then some md else none
  | none => none

/-- Object's `initialize` resolves to the native no-op, so a default `new` returns. -/
def initDispatchB (h : Heap) (k : ObjId) : Bool :=
  (Interp.methodOn h k "initialize").any fun p =>
    p.2.builtin == some "BasicObject#initialize" && !p.2.undefined

def RootInitOk (D : DefTable) (h : Heap) : Prop :=
  rootInitFreeB D = true → initDispatchB h Boot.objectId = true

def rootInitOkB (D : DefTable) (h : Heap) : Bool :=
  !rootInitFreeB D || initDispatchB h Boot.objectId

theorem rootInitOkB_sound {D : DefTable} {h : Heap} (hb : rootInitOkB D h = true) : RootInitOk D h := by
  intro hf
  simpa only [rootInitOkB, hf, Bool.not_true, Bool.false_or] using hb

theorem initDispatchB_userInit {h : Heap} {k : ObjId} (hd : initDispatchB h k = true) :
    userInit? h k = none := by
  unfold initDispatchB at hd
  unfold userInit?
  cases hl : Interp.methodOn h k "initialize" with
  | none => rfl
  | some p =>
    rw [hl] at hd
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hd
    simp [hd.1]

theorem RootInitOk.userInit {D : DefTable} {h : Heap} (hp : RootInitOk D h)
    (hf : rootInitFreeB D = true) : userInit? h Boot.objectId = none :=
  initDispatchB_userInit (hp hf)

theorem RootInitOk.transport {D D' : DefTable} {h h' : Heap} (hp : RootInitOk D h)
    (hd : rootInitFreeB D' = true → rootInitFreeB D = true)
    (hm : Interp.methodOn h' Boot.objectId "initialize" = Interp.methodOn h Boot.objectId "initialize") :
    RootInitOk D' h' := by
  intro hf
  simpa only [initDispatchB, hm] using hp (hd hf)

theorem RootInitOk.ext {D : DefTable} {m n : Machine} (hp : RootInitOk D m.heap) (he : Ext m n)
    (hc : Proof.ChainsIn m.heap) :
    RootInitOk D n.heap :=
  hp.transport id (he.methodOn_eq hc _ _)

#print axioms rootInitOkB_sound
end Checker.Soundness
