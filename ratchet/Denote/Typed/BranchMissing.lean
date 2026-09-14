import Denote.Typed.Run
import Denote.JoinState

/-! An omitted else returns nil immediately, preserving the condition's environment. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemA.ifNoElse {Γ Γc Γt : Env} {c t : Ratchet.Expr} {σ τ : Ty}
    (hc : SemSafeA Γ c σ Γc) (ht : SemSafeA Γc t τ Γt) :
    SemSafeA Γ (.if' c t none) (joinT τ .nilT) (joinEnv Γt Γc) := by
  apply semSafe_of_runSpec
  intro m hm
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ =
      .next (pushK [.ifK (toRuby t) none] (evalFrom m c)) from rfl)
  apply RunSpec.bind hc hm (by intro k hk tag; simp_all)
  intro a n hn
  cases a with
  | val v =>
    have hm' := hn.2.2 v rfl
    cases hv : v.truthy with
    | false =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.val .nil) n []) from by
          simp [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, hv, Interp.withCtl])
      exact RunSpec.answer ⟨hn.1, denM_joinT_right (by simp [denM, isNilV]),
        fun _ h => by cases h; exact StateOk_joinEnv false hm'⟩
    | true =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (evalFrom n t) from by
          simp [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, hv, Interp.withCtl, evalFrom])
      exact ((ht.weaken (fun _ _ hs hd =>
        ⟨StateOk_joinEnv true hs, denM_joinT_left hd⟩)).runSpec hm').rebase hn.1
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by
        cases j <;> simp [Interp.stepFn, deliverA, Answer.ctl, Interp.unwind, Interp.withCtl])
    exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ h => by cases h⟩

#print axioms SemA.ifNoElse
end Ratchet.Denote.Typed
