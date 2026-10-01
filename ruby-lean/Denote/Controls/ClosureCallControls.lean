import Denote.Controls.ClosureStoredReturnControls
import Denote.Rules.Closure.Call
import Denote.Rules.Closure.StorePrefix

/-! Whole stored-lambda calls consume body safety at the actual captured activation.
The creation/assignment prefix pins capture identity; a code-bearing type alone does not. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureCallControls
open RubyCore Ratchet Ratchet.Denote ClosureStoredControls ClosureStoredReturnControls

private def bodyCtx : Ctx := ctx0.withoutRuntimeScope.withFrame none
private def binding (code : ClosureCode) (name : String) : Env :=
  [(name, .clos code .ivar0 .never)]

theorem stored_body_state {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (code : ClosureCode) (name : String) (hp : code.params = [])
    (hls : code.locals = []) (hl : code.lam = true) :
    StateOk bodyCtx (binding code name) .ivar0
      (pushMethodFrame (stored m code name) (frame m code name)) := by
  obtain ⟨n, hs, hn⟩ := stored_entry hm code name hp hls hl
  rw [callClosure_required_lambda (stored m code name) (payload m code) [] [] none none none
    (by simp [payload, reifiedClosure, hp, toRubyParams])
    (by simpa [payload, reifiedClosure] using hl) rfl] at hs
  cases hs
  exact StateOk_reCtl hn (stored m code name).ctl (stored m code name).kont

/-- The source local read, Proc dispatch, body, and return all compose. The body may
write captures, provided its checked output retains the stored binding's exact type. -/
theorem stored_call {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (code : ClosureCode) (name : String) (hp : code.params = [])
    (hls : code.locals = []) (hl : code.lam = true) {τ : Ty} (ht : FirstOrder τ = true)
    (hb : SemSafeCtxA bodyCtx (binding code name) .ivar0 code.body τ
      bodyCtx (binding code name) .ivar0) :
    RunSpec (stored m code name)
      (evalFrom (stored m code name) (.send (some (.var .lvar name)) "call" [] none))
      (binding code name) τ ctx0 .ivar0 := by
  have hs := stored_state hm code name
  apply local_lambda_call_runSpec name (stored_payload hm code name)
    (hs.procCall rfl) (by
      rw [stored, getLocal_setLocal_self
        (reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam)
        _ _ hm.frameInRange.2, setLocal_heap]
      simp only [reifiedMachine, classOf, pushHeap_get_self])
    (by simp [payload, reifiedClosure, hp, toRubyParams])
    (by simpa [payload, reifiedClosure] using hl) rfl
  apply currentClosureFrame_runSpec hs.frameInRange.2
    (by unfold RootUncaptured; rw [← currentFrame_headD hs.frameInRange.1]; exact (hs.runtime rfl).captured)
    rfl true _ _ [] ht
    (hb _ (stored_body_state hm code name hp hls hl))
  intro n v hr
  exact stored_main_return hm code name hls hr.1 (hr.2.2 v rfl)

theorem stored_integer_call {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (name : String) (value : Int) :
    let code : ClosureCode := ⟨[], [], .int value, true, by simp [paramEqAll, exprEq]⟩
    RunSpec (stored m code name)
      (evalFrom (stored m code name) (.send (some (.var .lvar name)) "call" [] none))
      (binding code name) .int ctx0 .ivar0 :=
  stored_call hm _ name rfl rfl rfl rfl SemSafeCtxA.intLit

/-- This pilot proves the complete source prefix, so its activation facts come from
allocation and assignment rather than being inferred from Ty.clos. No DJudge is admitted. -/
theorem stored_program (code : ClosureCode) (name : String) (hp : code.params = [])
    (hls : code.locals = []) (hl : code.lam = true) {τ : Ty} (ht : FirstOrder τ = true)
    (hb : SemSafeCtxA bodyCtx (binding code name) .ivar0 code.body τ
      bodyCtx (binding code name) .ivar0) :
    SemSafeCtxA ctx0 [] .ivar0 (.seq [
      .vasgn .lvar name (.send none "lambda" []
        (some (.block code.params code.locals code.body))),
      .send (some (.var .lvar name)) "call" [] none]) τ ctx0 (binding code name) .ivar0 := by
  intro m hm
  have h := closure_store_seq_runSpec hm code name (by rw [hl]; rfl)
    (.send (some (.var .lvar name)) "call" [] none)
    (stored_call hm code name hp hls hl ht hb)
  simpa only [hl, ↓reduceIte] using h

theorem boot_integer_program (hb : bootOkB = true) (value : Int) :
    StuckFree bootMachine (.seq [
      .vasgn .lvar "f" (.send none "lambda" [] (some (.block [] [] (.int value)))),
      .send (some (.var .lvar "f")) "call" [] none]) :=
  (stored_program ⟨[], [], .int value, true, by simp [paramEqAll, exprEq]⟩ "f"
    rfl rfl rfl rfl SemSafeCtxA.intLit).closed (stateOk_boot hb)

private def program (lam : Bool) (args : List Ratchet.Expr) : Ratchet.Expr := .seq [
  .vasgn .lvar "f" (.send none (if lam then "lambda" else "proc") []
    (some (.block [] [] (.int 1)))),
  .send (some (.var .lvar "f")) "call" args none]

#guard match Interp.run 50 (evalFrom bootMachine (program true [])) with
  | .value (.int 1) _ => true
  | _ => false
#guard Semantics.typeStuck (Interp.run 50 (evalFrom bootMachine (program true [.int 2])))
#guard match Interp.run 50 (evalFrom bootMachine (program false [.int 2])) with
  | .value (.int 1) _ => true
  | _ => false

-- §F51: singleton Proc#call wins over the payload, as in CRuby 4.0.5.
#guard match Interp.run 50 (evalFrom bootMachine (.seq [
    .vasgn .lvar "f" (.send none "lambda" [] (some (.block [] [] (.int 1)))),
    .defs (.var .lvar "f") "call" [] (.int 7),
    .send (some (.var .lvar "f")) "call" [] none])) with
  | .value (.int 7) _ => true
  | _ => false

#print axioms stored_body_state
#print axioms stored_call
#print axioms stored_integer_call
#print axioms stored_program
#print axioms boot_integer_program
end Ratchet.Denote.Typed.ClosureCallControls
