import Denote.Sem.Subclass.SubclassFrame
import Denote.Sem.Class.ClassHeap

/-! The actual fresh class-body frame: uncaptured, no inherited locals or block, empty
class ivars, and self at the new class object (not an instance of the new class). -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {m : Machine} {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref name name e body

theorem current_frame : (entry).currentFrame = freshModFrame m.heap.objs.size m.currentFrame.cref :=
  Subclass.current_frame

theorem frame_in_range : FrameInRange entry := Subclass.frame_in_range
theorem get_local (x : String) : (entry).getLocal x = .nil := Subclass.get_local x
theorem env_empty : EnvOk [] entry := Subclass.env_empty
theorem ivar_nil (x : String) : ivarOf (entry).heap (entry).currentFrame.self x = .nil := Subclass.ivar_nil x
theorem spine_empty : SelfSpineOk .ivar0 entry := Subclass.spine_empty
theorem frame_ok : FrameOk none entry := Subclass.frame_ok
theorem block_none : BlockTyOk none entry := Subclass.block_none

theorem self_type (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    SelfTyOk (some (.clsOf name)) entry := Subclass.self_type ho

theorem self_live : SelfLive entry := Subclass.self_live
theorem uncaptured : RootUncaptured entry := Subclass.uncaptured

theorem saved_frame {i : FrameId} (hi : i < m.frames.size) :
    (entry).frames.getD i default = m.frames.getD i default := Subclass.saved_frame hi

#print axioms env_empty
#print axioms spine_empty
#print axioms saved_frame
end Ratchet.Denote.FreshClass
