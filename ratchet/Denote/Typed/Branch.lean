import Denote.Typed.Compose
import Denote.JoinState

/-! The conditional rule, including conformance of the joined environment. -/

set_option autoImplicit false

namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemA.if' {Γ Γc Γ₁ Γ₂ : Env} {c t e : Ratchet.Expr} {σ τ₁ τ₂ : Ty}
    (hc : SemSafeA Γ c σ Γc) (ht : SemSafeA Γc t τ₁ Γ₁)
    (he : SemSafeA Γc e τ₂ Γ₂) :
    SemSafeA Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂) := by
  apply semSafe_frame (k := .ifK (toRuby t) (some (toRuby e)))
    (branch := fun v => if v.truthy then t else e) hc
  · intro v
    split
    · exact ht.weaken (fun _ _ hm hd =>
        ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)
    · exact he.weaken (fun _ _ hm hd =>
        ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)
  · intro k hk tag
    simp only [List.mem_singleton] at hk
    subst hk
    simp
  · intro m; rfl
  · intro m v
    simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont]
    cases hv : v.truthy <;>
      simp [hv, Interp.withCtl, evalFrom, toRuby]
  · intro m j
    cases j <;>
      simp [Interp.stepFn, deliverA, Answer.ctl, Interp.unwind, Interp.withCtl]

#print axioms SemA.if'

end Ratchet.Denote.Typed
