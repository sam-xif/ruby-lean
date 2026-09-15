import Denote.Typed.Context

/-! A declared class constant is read using the machine's lexical resolver. StateOk's
scope agreement connects that read to the published heap identity. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.constClass {κ : Ctx} {Γ : Env} {I : Ty} {c : Cls}
    (hc : c ∈ κ.classes) : SemSafeCtxA κ Γ I (.const c.name) (.clsOf c.name) κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  obtain ⟨k, hk, _⟩ := hm.classes c hc
  have hl : constLookup m.heap c.name = some (.ref k) := by
    have ho := classNamed_constOwn hk
    cases hp : m.heap.classPayload? Boot.objectId <;> simpa [constOwn, constLookup, hp] using ho
  have hr := (hm.constScope c.name).trans hl
  refine ⟨m, .ref k, ?_, .refl m, ?_, fun _ _ => hm⟩
  · simp only [constResolveAt] at hr
    simp only [Interp.stepFn, Interp.evalExpr, toRuby, evalFrom, currentFrame_reCtl, hr,
      Interp.withCtl, deliverA, Answer.ctl]
  · simp [AnsOk, denM, isClassRefNamed, hk]

#print axioms SemSafeCtxA.constClass
end Ratchet.Denote.Typed
