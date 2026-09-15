import Denote.Typed.BoundedRun
import Denote.JoinState

/-! Bounded expression composition for scoped recursive bodies. Closed subexpressions
can still use their ordinary semantic proof via `SemSafeCtxA.at`. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxAt.weaken {N : Nat} {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env}
    {I I₁ I₂ σ τ : Ty} {e : Ratchet.Expr}
    (h : SemSafeCtxAt N κ Γ I e σ κ₁ Γ₁ I₁)
    (hout : ∀ m v, StateOk κ₁ Γ₁ I₁ m → denM σ m v →
      StateOk κ₂ Γ₂ I₂ m ∧ denM τ m v) : SemSafeCtxAt N κ Γ I e τ κ₂ Γ₂ I₂ :=
  fun m hm => (h m hm).weaken hout

/-- A frame selects a following expression on values and propagates escapes. The selected
expression starts at the premise's outgoing state index, not the outer expression's. -/
theorem SemSafeCtxAt.frame {N : Nat} {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {sub out : Ratchet.Expr} {k : Kont} {branch : Value → Ratchet.Expr}
    (hp : SemSafeCtxAt N κ Γ I sub σ κ₁ Γ₁ I₁)
    (hb : ∀ v, SemSafeCtxAt N κ₁ Γ₁ I₁ (branch v) τ κ₂ Γ₂ I₂)
    (hK : RubyCore.Proof.CatchFree [k])
    (heval : ∀ m, Interp.stepFn (evalFrom m out) =
      .next (pushK [k] (evalFrom m sub)))
    (hval : ∀ m v, Interp.stepFn (deliverA (.val v) m [k]) =
      .next (evalFrom m (branch v)))
    (hesc : ∀ m j, Interp.stepFn (deliverA (.esc j) m [k]) =
      .next (deliverA (.esc j) m [])) : SemSafeCtxAt N κ Γ I out τ κ₂ Γ₂ I₂ := by
  intro m hm
  apply RunSpecAt.stepWithin (answerPoint_evalFrom _ _) (heval m)
  apply (hp m hm).bindSpec hK
  intro a n hr
  have hap : answerPoint (deliverA a n [k]) = none := by simp [answerPoint, deliverA]
  cases a with
  | val v => exact RunSpecAt.stepWithin hap (hval n v) ((hb v n (hr.2.2 v rfl)).rebase hr.1)
  | esc j =>
    exact RunSpecAt.stepWithin hap (hesc n j)
      (RunSpecAt.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩)


/- Both branches must return the same context and spine; only locals/result types are
joined here. Different declaration tables or ivar effects need their own join theorem. -/
theorem SemSafeCtxAt.if' {N : Nat} {κ κc κ' : Ctx} {Γ Γc Γ₁ Γ₂ : Env} {I Ic I' : Ty}
    {c t e : Ratchet.Expr} {σ τ₁ τ₂ : Ty}
    (hc : SemSafeCtxAt N κ Γ I c σ κc Γc Ic) (ht : SemSafeCtxAt N κc Γc Ic t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxAt N κc Γc Ic e τ₂ κ' Γ₂ I') :
    SemSafeCtxAt N κ Γ I (.if' c t (some e)) (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  apply SemSafeCtxAt.frame (k := .ifK (toRuby t) (some (toRuby e)))
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
    cases v.truthy <;> simp [Interp.withCtl, evalFrom]
  · intro m j
    cases j <;>
      simp [Interp.stepFn, deliverA, Answer.ctl, Interp.unwind, Interp.withCtl]


#print axioms SemSafeCtxAt.frame
#print axioms SemSafeCtxAt.if'
end Ratchet.Denote.Typed
