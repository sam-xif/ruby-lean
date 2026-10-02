import Denote.Judgment.Context

/-! Regexp literals: one allocation of a Regexp object. A pattern the model cannot parse
halts as unsupported, so the rule needs no static parse guard. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def rxObj (src : String) (opts : Nat) : Object :=
  { klass := Boot.regexpId, payload := .regexp src opts }

theorem SemSafeCtxA.regexpLit {κ : Ctx} {Γ : Env} {I : Ty} {src : String} {opts : Nat} :
    SemSafeCtxA κ Γ I (.regexpLit src opts) (.cls "Regexp") κ Γ I := by
  intro m hm
  cases hp : Rx.parse src opts with
  | error e =>
    exact RunSpec.unsupported (answerPoint_evalFrom _ _)
      (show Interp.stepFn (evalFrom m (.regexpLit src opts)) = .unsupported e by
        simp [evalFrom, toRuby, Interp.stepFn, Interp.evalExpr, hp])
  | ok r =>
    let M := reCtl { m with heap := pushHeap m.heap (rxObj src opts) } (.value (.ref m.heap.objs.size)) []
    have hstep : Interp.stepFn (evalFrom m (.regexpLit src opts)) = .next M := by
      simp [evalFrom, toRuby, Interp.stepFn, Interp.evalExpr, hp, M, reCtl, Interp.withCtl,
        Heap.alloc, pushHeap, rxObj]
    have hext : Ext m M :=
      (ext_push (m := m) (rxObj src opts) hm.sat hm.core.basicSelf
        (fun c => by simp [rxObj]) rfl rfl (by simpa [rxObj] using hm.core.regexpBasic)).trans
        (Ext_toReCtl _ _ _)
    have hs : StateOk κ Γ I M := StateOk_ext hm hext
      (stringPayloadOk_push hm.stringPayload (fun h => by simp [rxObj] at h; cases h))
      (arrayPayloadOk_push hm.arrayPayload (by simp [rxObj]))
      (hashPayloadOk_push hm.hashPayload (by simp [rxObj])) rfl
    have hanc : ∀ k, ancestors (pushHeap m.heap (rxObj src opts)) k = ancestors m.heap k :=
      Proof.ancestors_congr_grow hext.shapeAgree hext.size hm.sat
    have hcls : classOf (pushHeap m.heap (rxObj src opts)) (.ref m.heap.objs.size) = Boot.regexpId := by
      simp [classOf, pushHeap_get_self, rxObj]
    have hden : denM (.cls "Regexp") M (.ref m.heap.objs.size) := by
      show denM (.cls "Regexp") _ _
      rw [denM, isAName, hext.classNamed?_eq, hm.core.regexpNamed]
      show (ancestors (pushHeap m.heap (rxObj src opts)) _).contains _ = true
      rw [hcls, hanc]
      exact hm.core.regexpSelf
    apply RunSpec.step (answerPoint_evalFrom _ _) hstep
    exact RunSpec.answer (a := .val (.ref m.heap.objs.size)) (m := M) ⟨Framed.of_ext hext, hden, fun _ _ => hs⟩

#print axioms SemSafeCtxA.regexpLit
end Ratchet.Denote.Typed
