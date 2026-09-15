import Denote.Typed.PointClass
import Denote.Typed.ConstructorRun

/-! Published Point conformance now supplies allocation shape as well as actual code.
The remaining body premise is discharged at its annotations, for all Integer arguments. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

theorem constructor_run {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk callerCtx Γ I m) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hkont : m.kont = []) (x y : Int) :
    ∃ k n, classNamed? m.heap "Point" = some k ∧
      Interp.finishSend m (.ref k) .explicit "new" [.int x, .int y] .none = .next n ∧
      RunSpec m n Γ (.inst "Point" pointInitSpine) callerCtx I := by
  obtain ⟨k, md, site, dispatch, hp, hb, code, hi⟩ := constructor_code hm
  obtain ⟨j, hj, alloc⟩ := hm.allocators "Point" (by change "Point" ∈ ["Point"]; simp)
  have he : j = k := Option.some.inj (hj.symm.trans site.named)
  subst j
  have hconst (cn : String) : constGet? (initializerBodyCtx callerCtx "Point") cn =
      constGet? callerCtx cn :=
    (constGet?_empty (κ := initializerBodyCtx callerCtx "Point") rfl cn).trans
      (constGet?_empty rfl cn).symm
  obtain ⟨n, hn, hr⟩ := constructor_runSpec (κ := callerCtx) (ps := pointInitParams)
    (args := [.int x, .int y])
    (κb := initializerBodyCtx callerCtx "Point") hm (ReframeFO.empty hI rfl rfl rfl) rfl
    (ReframeFO.empty hI rfl rfl rfl) alloc site dispatch code hi hp hb rfl
    (by simp [pointInitParams, DenAll, denM, isIntV])
    (by simp [pointInitParams, FirstOrder, isAliasTy]) hconst rfl rfl rfl rfl hconst hΓ rfl rfl hkont
    initializer_body
  exact ⟨k, n, site.named, hn, hr⟩

#print axioms constructor_run
end Ratchet.Denote.Typed.PointClass
