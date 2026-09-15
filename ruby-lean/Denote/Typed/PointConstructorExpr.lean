import Denote.Typed.PointConstructor
import Denote.Typed.ConstructorExpr
import Denote.Typed.ClassConstant

/-! Constructor expressions, not just final dispatch. The receiver and arbitrary argument
expressions run first; only their proved types, never their syntax, feed the annotated body. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

theorem constructor_expr {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty}
    {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf "Point") callerCtx Γ₁ I₁)
    (ha : SemAllCtxA callerCtx Γ₁ I₁ args [.int, .int] callerCtx Γ₂ I₂)
    (hsite : (match toRuby recv with | .self' => .selfRecv | _ => .explicit) = SendSite.explicit)
    (hI : FirstOrder I₂ = true) (hΓ : ∀ p ∈ Γ₂, FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none)
      (.inst "Point" pointInitSpine) callerCtx Γ₂ I₂ := by
  exact hr.newInst (c := classWithMethod initClass getter) (d := initDecl) (ps := pointInitParams) ha
    (by cases recv <;> first | rfl | cases hsite)
    (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
    (by change initDecl ∈ [getter, initDecl]; simp) rfl (by decide)
    (by change "Point" ∈ ["Point"]; simp) rfl (by simp [pointInitParams, FirstOrder, isAliasTy])
    rfl (by decide) initializer_body (main_guard hI hΓ)

theorem const_point {Γ : Env} {I : Ty} :
    SemSafeCtxA callerCtx Γ I (.const "Point") (.clsOf "Point") callerCtx Γ I :=
  SemSafeCtxA.constClass (c := classWithMethod initClass getter)
    (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)

def newExpr (x y : Int) : Ratchet.Expr :=
  .send (some (.const "Point")) "new" [.int x, .int y] none

theorem new_sem {Γ : Env} {I : Ty} (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (x y : Int) :
    SemSafeCtxA callerCtx Γ I (newExpr x y) (.inst "Point" pointInitSpine) callerCtx Γ I :=
  constructor_expr const_point (.cons .intLit (.cons .intLit .nil rfl) rfl) rfl hI hΓ

/-- The complete class statement followed by construction, through both real sequence frames. -/
theorem class_new_run {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk ctx0 Γ I m) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (x y : Int) :
    RunSpec m (evalFrom m (.seq [program, newExpr x y])) Γ
      (.inst "Point" pointInitSpine) callerCtx I :=
  (runSpec hm hI hΓ).thenSeq (.last (new_sem hI hΓ x y))

#print axioms constructor_expr
#print axioms class_new_run
end Ratchet.Denote.Typed.PointClass
