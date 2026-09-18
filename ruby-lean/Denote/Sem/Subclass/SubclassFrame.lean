import Denote.Sem.Subclass.SubclassNames

/-! Fresh body-frame facts depend on allocation/frame shape, not on which class is the
superclass. Global self typing is restricted to registration in Object's namespace. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof.Judgment

variable {m : Machine} {d parent eParent : ObjId} {cref : List ObjId}
variable {name q : String} {body : RubyCore.Expr}
local notation "entry" => machine m d cref name q parent eParent body

theorem current_frame : (entry).currentFrame = freshModFrame m.heap.objs.size cref := by
  simp [machine, Machine.currentFrame, Array.getD_eq_getD_getElem?]

theorem frame_in_range : FrameInRange entry := by simp [FrameInRange, machine]

theorem get_local (x : String) : (entry).getLocal x = .nil := by
  simp [Machine.getLocal, Machine.getLocal.go, machine, freshModFrame, Array.getD_eq_getD_getElem?]

theorem env_empty : EnvOk [] entry := by
  refine ⟨?_, ?_⟩
  · intro x τ hx; simp [envGet?] at hx
  · intro x _; exact get_local x

theorem ivar_nil (x : String) : ivarOf (entry).heap (entry).currentFrame.self x = .nil := by
  rw [current_frame]
  simp [freshModFrame, machine, ivarOf, get_class, classObjE, classObj]

theorem spine_empty : SelfSpineOk .ivar0 entry := by
  refine ⟨?_, fun x _ _ => ivar_nil x⟩
  simp [denSpine, denSpineFrom]

theorem frame_ok : FrameOk none entry := by simp [FrameOk, current_frame, freshModFrame]
theorem block_none : BlockTyOk none entry := by simp [BlockTyOk, current_frame, freshModFrame]

theorem self_type (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    SelfTyOk (some (.clsOf name)) (machine m Boot.objectId cref name q parent eParent body) := by
  rw [SelfTyOk, current_frame, denM]
  change isClassRefNamed (heap m.heap Boot.objectId name q parent eParent) (.ref m.heap.objs.size) name = true
  simp only [isClassRefNamed, named_fresh ho, beq_self_eq_true]

theorem self_live : SelfLive entry := by
  intro o ho
  rw [current_frame] at ho
  change Value.ref m.heap.objs.size = .ref o at ho
  cases ho
  change m.heap.objs.size < (heap m.heap d name q parent eParent).objs.size
  rw [size]; omega

theorem uncaptured : RootUncaptured entry := by
  simp [RootUncaptured, machine, freshModFrame, Array.getD_eq_getD_getElem?]

theorem saved_frame {i : FrameId} (hi : i < m.frames.size) :
    (entry).frames.getD i default = m.frames.getD i default := by
  simp [machine, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]

#print axioms env_empty
#print axioms spine_empty
#print axioms self_type
#print axioms saved_frame
end Ratchet.Denote.Subclass
