import Denote.Typed.PointClass
import Denote.Typed.ConstructorResolve

/-! Published Point conformance now supplies allocation shape as well as actual code.
The remaining body premise is discharged at its annotations, for all Integer arguments. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

theorem initializer_consts (cn : String) : constGet? (initializerBodyCtx callerCtx "Point") cn =
    constGet? callerCtx cn :=
  (constGet?_empty (κ := initializerBodyCtx callerCtx "Point") rfl cn).trans
    (constGet?_empty rfl cn).symm

theorem constructor_runValues {Γ : Env} {I : Ty} {m : Machine} {args : List Value}
    (hm : StateOk callerCtx Γ I m) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hkont : m.kont = [])
    (hargs : DenAll (pointInitParams.map (·.2)) m args) :
    ∃ k n, classNamed? m.heap "Point" = some k ∧
      Interp.finishSend m (.ref k) .explicit "new" args .none = .next n ∧
      RunSpec m n Γ (.inst "Point" pointInitSpine) callerCtx I :=
  declared_constructor_run (c := classWithMethod initClass getter) (d := initDecl) hm
    (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
    (by change initDecl ∈ [getter, initDecl]; simp) rfl (by decide)
    (by change "Point" ∈ ["Point"]; simp) rfl (by simp [pointInitParams, FirstOrder, isAliasTy])
    initializer_body (ReframeFO.empty hI rfl rfl rfl) rfl rfl rfl rfl initializer_consts
    hΓ (by decide) hkont hargs

theorem constructor_run {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk callerCtx Γ I m) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hkont : m.kont = []) (x y : Int) :
    ∃ k n, classNamed? m.heap "Point" = some k ∧
      Interp.finishSend m (.ref k) .explicit "new" [.int x, .int y] .none = .next n ∧
      RunSpec m n Γ (.inst "Point" pointInitSpine) callerCtx I :=
  constructor_runValues hm hI hΓ hkont (by simp [pointInitParams, DenAll, denM, isIntV])

#print axioms constructor_runValues
#print axioms constructor_run
end Ratchet.Denote.Typed.PointClass
