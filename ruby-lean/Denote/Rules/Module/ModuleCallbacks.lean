import Denote.Rules.Class.ClassCallbacks

/-! Fresh module prefix: the native const_added hook runs through real dispatch, then
constClassK (no superclass, so no inherited) pushes the ordinary body frame. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem module_callbacks_runSpec {origin m : Machine} {κ : Ctx} {Γ : Env} {I τ : Ty}
    {k : ObjId} {name : String} {body : RubyCore.Expr}
    (hq : classHooksQuietB m.heap = true) (hc : Proof.ChainsIn m.heap)
    (hl : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hp : m.preludeMode = false) (ho : m.currentFrame.libraryOrigin = false)
    (hb : RunSpec origin (classCallbackBody m k body) Γ τ κ I) :
    RunSpec origin
      { m with
        ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym name] none [],
        kont := .constClassK k none name body :: m.kont } Γ τ κ I := by
  let added := { m with kont := .constClassK k none name body :: m.kont }
  obtain hs | ⟨msg, hs⟩ := stepFn_class_hook (m := added) (arg := .sym name)
    (by simp [classHookNames] : ("const_added", "Module#const_added") ∈ classHookNames) hq hc hl
  · apply RunSpec.step (show answerPoint _ = none from rfl) hs
    exact RunSpec.step (show answerPoint _ = none from rfl)
      (show Interp.stepFn { added with ctl := .value .nil } = _ from
        pushClassFrame_ordinary (m := { m with ctl := .value .nil }) hp ho) hb
  · exact RunSpec.unsupported (show answerPoint _ = none from rfl) hs

#print axioms module_callbacks_runSpec
end Ratchet.Denote.Typed
