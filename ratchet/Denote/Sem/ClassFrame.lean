import Denote.Sem.ClassHeap

/-! The actual fresh class-body frame: uncaptured, no inherited locals or block, empty
class ivars, and self at the new class object (not an instance of the new class). -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {m : Machine} {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref name name e body

theorem current_frame : (entry).currentFrame = freshModFrame m.heap.objs.size m.currentFrame.cref := by
  simp [freshClsMachine, Machine.currentFrame, Array.getD_eq_getD_getElem?]

theorem frame_in_range : FrameInRange entry := by
  simp [FrameInRange, freshClsMachine]

theorem get_local (x : String) : (entry).getLocal x = .nil := by
  simp [Machine.getLocal, Machine.getLocal.go, freshClsMachine, freshModFrame,
    Array.getD_eq_getD_getElem?]

theorem env_empty : EnvOk [] entry := by
  refine ⟨?_, ?_⟩
  · intro x τ hx; simp [envGet?] at hx
  · intro x _; exact get_local x

theorem ivar_nil (x : String) : ivarOf (entry).heap (entry).currentFrame.self x = .nil := by
  rw [current_frame]
  simp [freshModFrame, freshClsMachine, ivarOf, Proof.Judgment.freshClsHeap_get_k,
    Proof.Judgment.clsObjE]

theorem spine_empty : SelfSpineOk .ivar0 entry := by
  refine ⟨?_, fun x _ => ivar_nil x⟩
  simp [denSpine, denSpineFrom]

theorem frame_ok : FrameOk none entry := by
  simp [FrameOk, current_frame, freshModFrame]

theorem block_none : BlockTyOk none entry := by
  simp [BlockTyOk, current_frame, freshModFrame]

theorem self_type (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    SelfTyOk (some (.clsOf name)) entry := by
  rw [SelfTyOk, current_frame, denM]
  change isClassRefNamed (freshClsHeap m.heap Boot.objectId name name e)
    (.ref m.heap.objs.size) name = true
  simp only [isClassRefNamed, classNamed_freshClass ho (lt_size_of_classPayload ho), beq_self_eq_true]

theorem self_live : SelfLive entry := by
  intro o ho
  rw [current_frame] at ho
  change Value.ref m.heap.objs.size = .ref o at ho
  cases ho
  change m.heap.objs.size < (freshClsHeap m.heap Boot.objectId name name e).objs.size
  rw [Proof.Judgment.freshClsHeap_size]
  omega

theorem uncaptured : RootUncaptured entry := by
  simp [RootUncaptured, freshClsMachine, freshModFrame, Array.getD_eq_getD_getElem?]

theorem saved_frame {i : FrameId} (hi : i < m.frames.size) :
    (entry).frames.getD i default = m.frames.getD i default := by
  simp [freshClsMachine, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]

#print axioms env_empty
#print axioms spine_empty
#print axioms saved_frame
end Ratchet.Denote.FreshClass
