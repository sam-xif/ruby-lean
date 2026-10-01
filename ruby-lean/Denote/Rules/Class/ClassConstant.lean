import Denote.Judgment.Context

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
  · have hr' : Interp.lexicalConstant (evalFrom m (.const c.name)) c.name = some (.ref k) := hr
    change (match Interp.lexicalConstant (evalFrom m (.const c.name)) c.name with
      | some v => StepResult.next (Interp.withCtl (evalFrom m (.const c.name)) (.value v))
      | none => _) = _
    rw [hr']
    rfl
  · simp [AnsOk, denM, isClassRefNamed, hk]

#print axioms SemSafeCtxA.constClass
end Ratchet.Denote.Typed
