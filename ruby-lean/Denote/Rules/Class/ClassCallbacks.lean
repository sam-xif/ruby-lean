import Denote.Judgment.Run
import Denote.Sem.Class.ClassRegistration
import Denote.Sem.Instance.ClassHookDispatch

/-! Repair the fresh-class prefix while retaining the existing body/return contract.
Both native hooks run through real dispatch before the original class frame is pushed. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshModFrame)

def classCallbackBody (m : Machine) (k : ObjId) (body : RubyCore.Expr) : Machine :=
  { m with
    frames := m.frames.push (freshModFrame k m.currentFrame.cref),
    stack := m.frames.size :: m.stack, kont := .frameK m.frames.size :: m.kont,
    ctl := .eval body }

theorem pushClassFrame_ordinary {m : Machine} {k : ObjId} {name : String} {body : RubyCore.Expr}
    (hp : m.preludeMode = false) (ho : m.currentFrame.libraryOrigin = false) :
    Interp.pushClassFrame m k name body =
      .next (classCallbackBody m k body) := by
  simp only [classCallbackBody, freshModFrame, Interp.pushClassFrame,
    Interp.libraryBodyGate, ho, hp,
    Bool.not_false, Bool.true_or, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem stepFn_classBodyK {m : Machine} {k : ObjId} {name : String} {body : RubyCore.Expr}
    (hp : m.preludeMode = false) (ho : m.currentFrame.libraryOrigin = false) :
    Interp.stepFn { m with ctl := .value .nil, kont := .classBodyK k name body :: m.kont } =
      .next (classCallbackBody m k body) := by
  change Interp.pushClassFrame { m with ctl := .value .nil } k name body = _
  exact pushClassFrame_ordinary hp ho

theorem class_callbacks_runSpec {origin m : Machine} {κ : Ctx} {Γ : Env} {I τ : Ty}
    {k : ObjId} {name : String} {body : RubyCore.Expr}
    (hq : classHooksQuietB m.heap = true) (hc : Proof.ChainsIn m.heap)
    (hl : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hp : m.preludeMode = false) (ho : m.currentFrame.libraryOrigin = false)
    (hb : RunSpec origin (classCallbackBody m k body) Γ τ κ I) :
    RunSpec origin
      { m with
        ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym name] none [],
        kont := .constClassK k (some Boot.objectId) name body :: m.kont } Γ τ κ I := by
  let added := { m with kont := .constClassK k (some Boot.objectId) name body :: m.kont }
  let inherited := { m with kont := .classBodyK k name body :: m.kont }
  obtain hs | ⟨msg, hs⟩ := stepFn_class_hook (m := added) (arg := .sym name)
    (by simp [classHookNames] : ("const_added", "Module#const_added") ∈ classHookNames) hq hc hl
  · apply RunSpec.step (show answerPoint _ = none from rfl) hs
    apply RunSpec.step (show answerPoint _ = none from rfl)
      (show Interp.stepFn { added with ctl := .value .nil } =
        .next { inherited with ctl := .send (.ref Boot.objectId) .reflective "inherited" [.ref k] none [] } from rfl)
    obtain hi | ⟨msg, hi⟩ := stepFn_class_hook (m := inherited) (arg := .ref k)
      (by simp [classHookNames] : ("inherited", "Class#inherited") ∈ classHookNames) hq hc hl
    · apply RunSpec.step (show answerPoint _ = none from rfl) hi
      exact RunSpec.step (show answerPoint _ = none from rfl) (stepFn_classBodyK hp ho) hb
    · exact RunSpec.unsupported (show answerPoint _ = none from rfl) hi
  · exact RunSpec.unsupported (show answerPoint _ = none from rfl) hs

#print axioms stepFn_classBodyK
#print axioms class_callbacks_runSpec
end Ratchet.Denote.Typed
