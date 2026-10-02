import Denote.Sem.Class.ClassCoreActual
import Denote.Rules.Class.ClassCallbacks

/-! Retain the original freshModFrame conformance at the actual callback-body entry. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof.Judgment
variable {p : ObjId}

/-- The body machine after both native callbacks, with the named/attached heap. -/
def machine (m : Machine) (name : String) (e : ObjId) (body : RubyCore.Expr)
    (p : ObjId := Boot.objectId) : Machine :=
  { m with
    heap := heap m name e p,
    frames := m.frames.push (freshModFrame m.heap.objs.size m.currentFrame.cref),
    stack := m.frames.size :: m.stack, kont := .frameK m.frames.size :: m.kont,
    ctl := .eval body }

theorem machine_callback (m : Machine) (name : String) (e : ObjId) (body : RubyCore.Expr) :
    machine m name e body p = Typed.classCallbackBody { m with heap := heap m name e p }
      m.heap.objs.size body := rfl

variable {m : Machine} {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => machine m name e body p

theorem current_frame : (entry).currentFrame = freshModFrame m.heap.objs.size m.currentFrame.cref := by
  simp [machine, Machine.currentFrame, Array.getD_eq_getD_getElem?]

theorem frame_in_range : FrameInRange entry := by simp [FrameInRange, machine]

theorem get_local (x : String) : (entry).getLocal x = .nil := by
  simp [Machine.getLocal, Machine.getLocal.go, Machine.localFrameId, Machine.localFrameId.go,
    machine, freshModFrame, Array.getD_eq_getD_getElem?]

theorem env_empty : EnvOk [] entry := by
  refine ⟨?_, ?_⟩
  · intro x τ hx; simp [envGet?] at hx
  · intro x _; exact get_local x

theorem ivar_nil (hd : m.lexicalNamespace < m.heap.objs.size) (x : String) :
    ivarOf (entry).heap (entry).currentFrame.self x = .nil := by
  rw [current_frame]
  simp [freshModFrame, machine, ivarOf, get_class hd, namedObject]

theorem spine_empty (hd : m.lexicalNamespace < m.heap.objs.size) : SelfSpineOk .ivar0 entry := by
  refine ⟨?_, fun x _ _ => ivar_nil hd x⟩
  simp [denSpine, denSpineFrom]

theorem frame_ok : FrameOk none entry := by simp [FrameOk, current_frame, freshModFrame]
theorem block_none : BlockTyOk none entry := by simp [BlockTyOk, current_frame, freshModFrame]

theorem self_type (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    SelfTyOk (some (.clsOf name)) entry := by
  rw [SelfTyOk, current_frame, denM]
  change isClassRefNamed (heap m name e p) (.ref m.heap.objs.size) name = true
  simp only [isClassRefNamed, named_fresh htop ho, beq_self_eq_true]

theorem self_live : SelfLive entry := by
  intro o ho
  rw [current_frame] at ho
  change Value.ref m.heap.objs.size = .ref o at ho
  cases ho
  change m.heap.objs.size < (heap m name e p).objs.size
  rw [size]; omega

theorem uncaptured : RootUncaptured entry := by
  simp [RootUncaptured, machine, freshModFrame, Array.getD_eq_getD_getElem?]

theorem saved_frame {i : FrameId} (hi : i < m.frames.size) :
    (entry).frames.getD i default = m.frames.getD i default := by
  simp [machine, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]

theorem local_alias : (entry).currentFrame.localAlias = none := by
  rw [current_frame]; rfl

theorem captured_live : CaptureLive entry (entry).currentFrame.captured := by
  rw [current_frame]
  exact CaptureLive.none

theorem root_clean (hp : RootClean m) : RootClean entry := hp

#print axioms local_alias
#print axioms captured_live
#print axioms root_clean
#print axioms env_empty
#print axioms spine_empty
#print axioms self_type
#print axioms saved_frame
end Ratchet.Denote.FreshClassActual
