import Denote.Rules.Method.FlowEntry
import Denote.Rules.Method.FlowCall
import Denote.Rules.Method.FlowSequence
import Denote.Controls.BoundCallbackControls

/-! General method-flow rules retain copied callback identity across real local
overwrites, repeated calls and receiver evaluation. All bodies are proved uniformly
for every checked callback with an Integer parameter, before choosing its capture. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.CallbackAliasControls
open RubyCore Ratchet Ratchet.Denote

private def fr : Ratchet.Frame := ⟨"Object", "Object", "run", false⟩
private def callExpr (x : String) (n : Int) : Ratchet.Expr :=
  .send (some (.var .lvar x)) "call" [.int n] none
private def copyExpr : Ratchet.Expr := .vasgn .lvar "copy" (.var .lvar "b")
private def wipeExpr : Ratchet.Expr := .vasgn .lvar "b" .nil
def copiedBody : Ratchet.Expr := .seq [copyExpr, wipeExpr, callExpr "copy" 5, callExpr "copy" 7]
def restoredBody : Ratchet.Expr := .seq [copyExpr, wipeExpr,
  .vasgn .lvar "b" (.var .lvar "copy"), callExpr "b" 5]
def receiverBody : Ratchet.Expr :=
  .send (some (.seq [copyExpr, wipeExpr, .var .lvar "copy"])) "call" [.int 5] none
private def wipeCopyArg : Ratchet.Expr := .seq [.vasgn .lvar "copy" .nil, .int 5]
def savedBody : Ratchet.Expr := .seq [copyExpr,
  .send (some (.var .lvar "b")) "call" [wipeCopyArg] none, callExpr "b" 7]

private def binding (code : ClosureCode) : Env := [("b", .clos code .ivar0 .never)]
private def copied (code : ClosureCode) : Env :=
  [("b", .clos code .ivar0 .never), ("copy", .clos code .ivar0 .never)]
private def wiped (code : ClosureCode) : Env := [("b", .nilT), ("copy", .clos code .ivar0 .never)]
private def wipedCopy (code : ClosureCode) : Env := [("b", .clos code .ivar0 .never), ("copy", .nilT)]

private theorem copy_typed {Γ : Env} (cb : CheckedCallback ctx0 Γ .ivar0) :
    SemMethodFlow cb fr (binding cb.code) ⟨["b"]⟩ copyExpr (.clos cb.code .ivar0 .never) true
      (copied cb.code) ⟨["copy", "b"]⟩ :=
  (SemMethodFlow.var _ rfl rfl).vasgn rfl rfl rfl rfl

private theorem wipe_typed {Γ : Env} (cb : CheckedCallback ctx0 Γ .ivar0) :
    SemMethodFlow cb fr (copied cb.code) ⟨["copy", "b"]⟩ wipeExpr .nilT false
      (wiped cb.code) ⟨["copy"]⟩ :=
  (SemMethodFlow.nilLit _).vasgn rfl rfl rfl rfl

private theorem call_typed {Γ Γm : Env} (cb : CheckedCallback ctx0 Γ .ivar0)
    {facts : CallbackFacts} (x : String) (n : Int) (hx : facts.aliases.contains x = true)
    (hg : envGet? Γm x = some (.clos cb.code .ivar0 .never))
    (ht : activationReturnB Γm = true) (hp : cb.params = [("x", .int)]) :
    SemMethodFlow cb fr Γm facts (callExpr x n) cb.ret false Γm facts := by
  have hv := SemMethodFlow.var (cb := cb) (fr := fr) facts hg rfl
  rw [hx] at hv
  exact hv.call (SemMethodFlow.intLit facts n) hp ht rfl rfl rfl

theorem copied_typed {Γ : Env} (cb : CheckedCallback ctx0 Γ .ivar0)
    (hp : cb.params = [("x", .int)]) :
    SemMethodFlow cb fr (binding cb.code) ⟨["b"]⟩ copiedBody cb.ret false
      (wiped cb.code) ⟨["copy"]⟩ :=
  .sequence (.cons (copy_typed cb) (.cons (wipe_typed cb)
    (.cons (call_typed cb "copy" 5 rfl rfl rfl hp) (.last (call_typed cb "copy" 7 rfl rfl rfl hp)))))

theorem restored_typed {Γ : Env} (cb : CheckedCallback ctx0 Γ .ivar0)
    (hp : cb.params = [("x", .int)]) :
    SemMethodFlow cb fr (binding cb.code) ⟨["b"]⟩ restoredBody cb.ret false
      (copied cb.code) ⟨["b", "copy"]⟩ := by
  have restore : SemMethodFlow cb fr (wiped cb.code) ⟨["copy"]⟩
      (.vasgn .lvar "b" (.var .lvar "copy")) (.clos cb.code .ivar0 .never) true
      (copied cb.code) ⟨["b", "copy"]⟩ :=
    (SemMethodFlow.var _ rfl rfl).vasgn rfl rfl rfl rfl
  exact .sequence (.cons (copy_typed cb) (.cons (wipe_typed cb)
    (.cons restore (.last (call_typed cb "b" 5 rfl rfl rfl hp)))))

theorem receiver_typed {Γ : Env} (cb : CheckedCallback ctx0 Γ .ivar0)
    (hp : cb.params = [("x", .int)]) :
    SemMethodFlow cb fr (binding cb.code) ⟨["b"]⟩ receiverBody cb.ret false
      (wiped cb.code) ⟨["copy"]⟩ := by
  have recv : SemMethodFlow cb fr (binding cb.code) ⟨["b"]⟩
      (.seq [copyExpr, wipeExpr, .var .lvar "copy"]) (.clos cb.code .ivar0 .never) true
      (wiped cb.code) ⟨["copy"]⟩ :=
    .sequence (.cons (copy_typed cb) (.cons (wipe_typed cb) (.last (SemMethodFlow.var _ rfl rfl))))
  exact recv.call (SemMethodFlow.intLit _ 5) hp rfl rfl rfl rfl

theorem saved_typed {Γ : Env} (cb : CheckedCallback ctx0 Γ .ivar0)
    (hp : cb.params = [("x", .int)]) :
    SemMethodFlow cb fr (binding cb.code) ⟨["b"]⟩ savedBody cb.ret false
      (wipedCopy cb.code) ⟨["b"]⟩ := by
  have arg : SemMethodFlow cb fr (copied cb.code) ⟨["copy", "b"]⟩ wipeCopyArg .int false
      (wipedCopy cb.code) ⟨["b"]⟩ :=
    .sequence (.cons ((SemMethodFlow.nilLit _).vasgn rfl rfl rfl rfl)
      (.last (SemMethodFlow.intLit _ 5)))
  have first := (SemMethodFlow.var (cb := cb) (fr := fr) ⟨["copy", "b"]⟩
    (Γm := copied cb.code) (x := "b") rfl rfl).call (name := "call") arg hp rfl rfl rfl rfl
  exact .sequence (.cons (copy_typed cb) (.cons first (.last (call_typed cb "b" 7 rfl rfl rfl hp))))

/-- A nil-typed local cannot be claimed as a callback alias in a conforming method,
even when the method still has a valid implicit block available to yield. -/
theorem nil_alias_rejected {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {frame : Ratchet.Frame} {origin m : Machine}
    (hm : MethodActivation cb frame Γm origin m) (x : String)
    (hg : envGet? Γm x = some .nilT) : ¬ CallbackFactsOk ⟨[x]⟩ m := by
  intro hf
  obtain ⟨o, _, hb, _⟩ := hm.callback
  have hrecv := hf x (by simp)
  have href : m.getLocal x = .ref o := Option.some.inj (hrecv.block.symm.trans hb)
  have hd := denM_getLocal hm.method hg rfl
  rw [href] at hd
  simp [denM, isNilV] at hd

private def cb := BoundCallbackControls.callback
private def allocated (m : Machine) : Machine := reifiedMachine m (toRubyParams cb.code.params)
  cb.code.locals (toRuby cb.code.body) cb.code.lam
private def method (m : Machine) (e : Ratchet.Expr) : MethodDef :=
  { params := [.block (some "b")], body := toRuby e, owner := m.currentFrame.defmod, cref := m.currentFrame.cref }
private def callStep (m : Machine) (e : Ratchet.Expr) : StepResult :=
  let entry := allocated m
  Interp.enterUserMethod entry entry.currentFrame.self "run" (method entry e) [] (some (.ref m.heap.objs.size))

private theorem call_boot {e : Ratchet.Expr} {Γm : Env} {facts : CallbackFacts}
    (he : SemMethodFlow cb fr (binding cb.code) ⟨["b"]⟩ e .int false Γm facts)
    (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m e) ctx0 .ivar0 := by
  let m := bootMachine.setLocal "total" (.int initial)
  have boot := stateOk_boot hb
  have hm : StateOk ctx0 [("total", .int)] .ivar0 m :=
    StateOk_setLocal (ρ := .int) boot (by simp [stripAlias, denM, isIntV])
      rfl rfl rfl (by intro y σ h; cases h)
  have hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cb.code.locals) cb.out) (allocated m) := by
    intro x τ hx
    by_cases hn : x = "total"
    · subst x
      exact frameBinds_setLocal_self bootMachine "total" (.int initial) boot.frameInRange.2
        (by rw [rootFrame_eq_currentFrame boot.frameInRange.1]; exact (boot.runtime rfl).captured)
    · simp [cb, BoundCallbackControls.callback, withoutNames, envGet?, Ne.symm hn] at hx
  have h := he.callBound (md := method (allocated m) e) (o := m.heap.objs.size)
    (cl := reifiedClosure m (toRubyParams cb.code.params) cb.code.locals (toRuby cb.code.body) cb.code.lam)
    (reified_state hm _ _ _ _) bootMachine_kont rfl rfl rfl rfl rfl rfl rfl rfl rfl hd
    (by simp only [reifiedMachine, pushHeap_get_self]) ⟨rfl, rfl, rfl, rfl⟩
    (by simp [classOf, reifiedMachine, pushHeap_get_self])
  exact h.rebase (.of_ext (reified_ext hm _ _ _ _))

theorem copied_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m copiedBody) ctx0 .ivar0 :=
  call_boot (copied_typed cb rfl) hb initial

theorem restored_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m restoredBody) ctx0 .ivar0 :=
  call_boot (restored_typed cb rfl) hb initial

theorem receiver_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m receiverBody) ctx0 .ivar0 :=
  call_boot (receiver_typed cb rfl) hb initial

theorem saved_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m savedBody) ctx0 .ivar0 :=
  call_boot (saved_typed cb rfl) hb initial

#print axioms copied_typed
#print axioms copied_from_boot
#print axioms restored_from_boot
#print axioms receiver_from_boot
#print axioms saved_from_boot
#print axioms nil_alias_rejected
end Ratchet.Denote.Typed.CallbackAliasControls
