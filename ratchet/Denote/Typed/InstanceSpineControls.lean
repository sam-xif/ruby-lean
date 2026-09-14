import Denote.Typed.InstanceEntry
import Denote.Sem.IvarMutation
import Denote.Typed.InstanceWrite
import Denote.Sanity

/-! An open instance type does not say that unmentioned fields are nil. This distinction
must survive the move from a receiver annotation into a method's self-spine. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem open_instance_not_complete {m : Machine} {cn x : String}
    (hn : isExactInst m.heap m.currentFrame.self cn = true)
    (hx : ivarOf m.heap m.currentFrame.self x = .int 7) :
    denM (.inst cn .ivar0) m m.currentFrame.self ∧ ¬ SelfSpineOk .ivar0 m := by
  refine ⟨by simpa only [denM, denSpineFrom, and_true] using hn, ?_⟩
  intro hs
  have hnil := hs.2 x rfl rfl
  rw [hx] at hnil
  cases hnil

-- The same receiver really has the field; this is not a dangling-reference example.
private def withExtra : Machine := Interp.bindIvar bootMachine "@extra" (.int 7)

-- Full-state witness: forgetting known fields is sound only with the open flag.
theorem boot_extra_open_state (hb : bootOkB = true) :
    StateOk { ctx0 with scope := { ctx0.scope with closedIvars := false } } [] .ivar0 withExtra ∧
      ivarOf withExtra.heap withExtra.currentFrame.self "@extra" = .int 7 := by
  have hm := stateOk_boot hb
  have ready := hm.runtime rfl
  have hw : StateOk ctx0 [] (.ivarCons "@extra" .int .ivar0) withExtra := by
    apply StateOk_bindIvar hm "@extra" (.int 7)
    · exact env_bindIvar hm.env (by intro y τ hy; cases hy)
    · exact selfSpine_bindIvar ready.self ready.live hm.selfSpine
        (by simp [denM, isIntV]) (by intro y τ _ hy; cases hy)
    · simpa only [BlockTyOk, ctx0, bindIvar_currentFrame] using hm.blockTy
    · trivial
    · intro x τ hx; rw [constGet?_empty (by rfl)] at hx; cases hx
    · intro owner x τ k hx; cases hx
  refine ⟨StateOk_forgetIvars hw, ?_⟩
  change ivarOf (Interp.bindIvar bootMachine "@extra" (.int 7)).heap
    (Interp.bindIvar bootMachine "@extra" (.int 7)).currentFrame.self "@extra" = _
  rw [bindIvar_currentFrame, ready.self]
  exact ivarOf_bindIvar_self ready.self ready.live

#guard isExactInst withExtra.heap withExtra.currentFrame.self "Object"
#guard (ivarOf withExtra.heap withExtra.currentFrame.self "@extra").identEq (.int 7)
#guard match Interp.run 10 (evalFrom withExtra (.var .ivar "@extra")) with
  | .value (.int 7) _ => true
  | _ => false
#guard match Interp.run 100 (evalFrom withExtra
    (.seq [.def' "read_extra" [] (.var .ivar "@extra"), .send none "read_extra" [] none])) with
  | .value (.int 7) _ => true
  | _ => false

#print axioms open_instance_not_complete
#print axioms boot_extra_open_state

private def getterCtx (I : Ty) : Ctx := instanceBodyCtx ctx0 ⟨"Point", "Point", "getX"⟩ I
#guard (getterCtx .ivar0).ivarReadTy .ivar0 "@extra" == .any
#guard (classBodyCtx ctx0 "Point").ivarReadTy .ivar0 "@extra" == .nilT
#guard (getterCtx (.ivarCons "@x" .int .ivar0)).ivarReadTy (.ivarCons "@x" .int .ivar0) "@x" == .int
#guard !ctxEqB ctx0 { ctx0 with scope := { ctx0.scope with closedIvars := false } }

-- The annotated getter still has its Integer body proof on an open receiver.
example {κ : Ctx} {Γ : Env} :
    SemSafeCtxA (instanceBodyCtx κ ⟨"Point", "Point", "getX"⟩ (.ivarCons "@x" .int .ivar0))
      Γ (.ivarCons "@x" .int .ivar0) (.var .ivar "@x") .int
      (instanceBodyCtx κ ⟨"Point", "Point", "getX"⟩ (.ivarCons "@x" .int .ivar0))
      Γ (.ivarCons "@x" .int .ivar0) := SemSafeCtxA.ivarRead

example {κ : Ctx} {Γ : Env} (hc : κ.scope.closedIvars = false) :
    SemSafeCtxA κ Γ .ivar0 (.var .ivar "@extra") .any κ Γ .ivar0 := by
  simpa [Ctx.ivarReadTy, ivarGet?, hc] using
    (SemSafeCtxA.ivarRead (κ := κ) (Γ := Γ) (I := .ivar0) (x := "@extra"))
end Ratchet.Denote.Typed
