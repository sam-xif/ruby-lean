import Ratchet.RootInit
import Denote.Ext
import RubyCore.Interp.Dispatch

/-! Root initialization is a heap contract indexed by the existing top-level def table.
It admits declared Object#initialize but never infers a body proof from its signature. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def RootInitOk (D : DefTable) (h : Heap) : Prop :=
  rootInitFreeB D = true → Interp.userInit? h Boot.objectId = none

def rootInitOkB (D : DefTable) (h : Heap) : Bool :=
  !rootInitFreeB D || (Interp.userInit? h Boot.objectId).isNone

theorem rootInitOkB_sound {D : DefTable} {h : Heap} (hb : rootInitOkB D h = true) : RootInitOk D h := by
  intro hf
  simpa only [rootInitOkB, hf, Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none] using hb

theorem RootInitOk.transport {D D' : DefTable} {h h' : Heap} (hp : RootInitOk D h)
    (hd : rootInitFreeB D' = true → rootInitFreeB D = true)
    (hm : Interp.methodOn h' Boot.objectId "initialize" = Interp.methodOn h Boot.objectId "initialize") :
    RootInitOk D' h' := by
  intro hf
  simpa only [Interp.userInit?, hm] using hp (hd hf)

theorem RootInitOk.ext {D : DefTable} {m n : Machine} (hp : RootInitOk D m.heap) (he : Ext m n) :
    RootInitOk D n.heap :=
  hp.transport id (by simp only [Interp.methodOn, he.payload, he.ancestors])

#print axioms rootInitOkB_sound
end Ratchet.Denote
