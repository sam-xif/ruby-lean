import Denote.Judgment.Context
import Denote.Sem.Core.JoinState

/-! The conditional rule, including conformance of the joined environment. -/

set_option autoImplicit false

namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/- Both branches must return the same context and spine; only locals/result types are
joined here. Different declaration tables or ivar effects need their own join theorem. -/
theorem SemSafeCtxA.if' {κ κc κ' : Ctx} {Γ Γc Γ₁ Γ₂ : Env} {I Ic I' : Ty}
    {c t e : Ratchet.Expr} {σ τ₁ τ₂ : Ty}
    (hc : SemSafeCtxA κ Γ I c σ κc Γc Ic) (ht : SemSafeCtxA κc Γc Ic t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxA κc Γc Ic e τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' c t (some e)) (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  apply SemSafeCtxA.frame (k := .ifK (toRuby t) (some (toRuby e)))
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

theorem SemA.if' {Γ Γc Γ₁ Γ₂ : Env} {c t e : Ratchet.Expr} {σ τ₁ τ₂ : Ty}
    (hc : SemSafeA Γ c σ Γc) (ht : SemSafeA Γc t τ₁ Γ₁)
    (he : SemSafeA Γc e τ₂ Γ₂) :
    SemSafeA Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂) :=
  semSafeA_iff_context.mpr ((semSafeA_iff_context.mp hc).if'
    (semSafeA_iff_context.mp ht) (semSafeA_iff_context.mp he))

#print axioms SemSafeCtxA.if'
#print axioms SemA.if'
end Ratchet.Denote.Typed
