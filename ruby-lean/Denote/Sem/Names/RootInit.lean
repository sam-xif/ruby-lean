import Ratchet.Guards.RootInit
import Denote.Ty.Ext
import RubyCore.Interp.Dispatch

/-! Root initialization is a heap contract indexed by the existing top-level def table.
It admits declared Object#initialize but never infers a body proof from its signature. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

/-- Proof-side classifier retained after constructor entry moved to queued
    ordinary dispatch. It records whether a user initializer exists; it is not
    an executable constructor shortcut. -/
def userInit? (h : Heap) (k : ObjId) : Option MethodDef :=
  match Interp.methodOn h k "initialize" with
  | some (_, md) => if md.builtin.isNone then some md else none
  | none => none

def RootInitOk (D : DefTable) (h : Heap) : Prop :=
  rootInitFreeB D = true → userInit? h Boot.objectId = none

def rootInitOkB (D : DefTable) (h : Heap) : Bool :=
  !rootInitFreeB D || (userInit? h Boot.objectId).isNone

theorem rootInitOkB_sound {D : DefTable} {h : Heap} (hb : rootInitOkB D h = true) : RootInitOk D h := by
  intro hf
  simpa only [rootInitOkB, hf, Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none] using hb

theorem RootInitOk.transport {D D' : DefTable} {h h' : Heap} (hp : RootInitOk D h)
    (hd : rootInitFreeB D' = true → rootInitFreeB D = true)
    (hm : Interp.methodOn h' Boot.objectId "initialize" = Interp.methodOn h Boot.objectId "initialize") :
    RootInitOk D' h' := by
  intro hf
  simpa only [userInit?, hm] using hp (hd hf)

theorem RootInitOk.ext {D : DefTable} {m n : Machine} (hp : RootInitOk D m.heap) (he : Ext m n)
    (hc : Proof.ChainsIn m.heap) :
    RootInitOk D n.heap :=
  hp.transport id (he.methodOn_eq hc _ _)

#print axioms rootInitOkB_sound
end Ratchet.Denote
