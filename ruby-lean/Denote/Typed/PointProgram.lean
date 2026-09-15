import Denote.Typed.PointConstructorExpr
import Denote.Typed.InstanceExpr

/-! Worked instance of the generic class, constructor, and method-call lemmas: all of 061.
This is a semantic program proof; class/initializer certificate admission remains separate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

def getExpr (x y : Int) : Ratchet.Expr := .send (some (newExpr x y)) "getX" [] none
def fullProgram (x y : Int) : Ratchet.Expr := .seq [program, getExpr x y]

theorem get_sem {Γ : Env} {I : Ty} (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (x y : Int) :
    SemSafeCtxA callerCtx Γ I (getExpr x y) .int callerCtx Γ I :=
  (new_sem hI hΓ x y).callMethodSig (c := classWithMethod initClass getter) (d := getter) (ps := [])
    .nil rfl
    (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
    (by change getter ∈ [getter, initDecl]; simp) (by decide)
    (by decide) rfl (by simp) rfl (by decide) getter_body (instanceCallB_of_mainCallB (main_guard hI hΓ))

theorem full_run {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk ctx0 Γ I m)
    (hI : FirstOrder I = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (x y : Int) :
    RunSpec m (evalFrom m (fullProgram x y)) Γ .int callerCtx I :=
  (runSpec hm hI hΓ).thenSeq (.last (get_sem hI hΓ x y))

theorem boot_full_run (hb : bootOkB = true) (x y : Int) :
    RunSpec bootMachine (evalFrom bootMachine (fullProgram x y)) [] .int callerCtx .ivar0 :=
  full_run (stateOk_boot hb) rfl (by simp) x y

#print axioms get_sem
#print axioms full_run
#print axioms boot_full_run
end Ratchet.Denote.Typed.PointClass
