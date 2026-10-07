import Books.TypeSoundness.Rules.Method.YieldInt

/-! Rung 094's actual method body: two yields, left-to-right argument evaluation,
saved receiver, native Integer addition and the real method return. The callback is
checked independently and may update captured caller values at stable types. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.YieldBody
open RubyCore Checker Checker.Soundness

def twice : Checker.Expr :=
  .send (some (.yield' [.int 1])) "+" [.yield' [.int 2]] none

private theorem int_value {m : Machine} {v : Value} (h : denM .int m v) :
    ∃ x, v = .int x := by cases v <;> simp_all [denM, isIntV]

/-- The complete body contract, conditional only on entry conformance and the checked
callback. Definition installation and source-call entry are still separate obligations. -/
theorem run {m : Machine} {κ : Ctx} {Γ Γb Γm : Env} {I : Ty}
    {cl : Closure} {name : String} {names : List String} {body : Checker.Expr}
    {o : ObjId} {fr : Checker.Frame} {code : ClosureCode}
    (hn : CallbackCaller κ Γ I cl [(name, .int)] names Γb m)
    (hm : StateOk (callbackMethodCtx κ fr code) Γm I m) (hs : CallbackMethodScope m)
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hblk : m.currentFrame.blk = some (.ref o)) (hproc : (m.heap.get o).payload = .proc cl)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (hmain : closureMainB κ I = true) (hfree : nameFreeN κ "+" = true)
    (hin : activationEnvB ([(name, .int)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true) (hmtys : activationReturnB Γm = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, .int)] ++ blockLocals cl.locals ++ Γ) I
      body .int (closureBodyCtx κ) Γb I) (fid : FrameId) :
    RunSpec (popMethodFrame m) (pushK [.frameK fid] (evalFrom m twice)) Γ .int κ I := by
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK "+" [toRuby (.yield' [.int 2])] .none .explicit, .frameK fid]
      (evalFrom m (.yield' [.int 1]))) from rfl)
  refine typed_yield_int_continue hn hm.frameInRange hne ?_ hblk hproc hp he
    hmain rfl hin hout hfix hb ?_ 1
  · intro k hmem tag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> simp
  · intro a n hfirst
    cases a with
    | esc j =>
      obtain ⟨exc, rfl, _⟩ := hfirst.2.1.only_raise
      exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl)
        (hfirst.methodReturn rfl fid)
    | val v =>
      obtain ⟨x, rfl⟩ := int_value hfirst.2.1
      have hn' := hn.next hfirst
      have hm' := hfirst.methodState hn.state hm hmain hs hmtys
      have hs' := hfirst.1.methodScope hn.state.frameInRange hs
      have hne' : n.stack.headD 0 ≠ (popMethodFrame n).stack.headD 0 := by
        simpa only [popMethodFrame, hfirst.1.stack] using hne
      apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
        (pushK [.argsK (.int x) .explicit "+" [] [] .none, .frameK fid]
          (evalFrom n (.yield' [.int 2]))) from rfl)
      refine typed_yield_int_continue hn' hm'.frameInRange hne' ?_
        (by rw [hfirst.1.active]; exact hblk) (hfirst.1.proc hproc) hp he
        hmain rfl hin hout hfix hb ?_ 2
      · intro k hmem tag
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> simp
      · intro a out hsecond
        have htotal : CallbackResultOk m Γ .int κ I a out := ⟨hfirst.1.trans hsecond.1, hsecond.2⟩
        cases a with
        | esc j =>
          obtain ⟨exc, rfl, _⟩ := hsecond.2.1.only_raise
          exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl)
            (htotal.methodReturn rfl fid)
        | val v =>
          obtain ⟨y, rfl⟩ := int_value hsecond.2.1
          have hm'' := hsecond.methodState hn'.state hm' hmain hs' hmtys
          let base := deliverA (.val (.int y)) out [.frameK fid]
          have hadd := invoke_int_add (site := .explicit)
            (StateOk_deliverA (a := .val (.int y)) (K := [.frameK fid]) hm'') x y hfree
          apply RunSpec.of_stepSpec (by rfl)
          change StepSpec (popMethodFrame m) Γ .int
            (Interp.invoke base (.int x) .explicit "+" [.int y] none []) κ I
          rw [hadd]
          have hsum : CallbackResultOk m Γ .int κ I (.val (.int (x + y))) out :=
            ⟨htotal.1, by simp [AnsOk, denM, isIntV], fun _ _ => hsecond.2.2 _ rfl⟩
          exact hsum.methodReturn rfl fid

#print axioms run
end Checker.Soundness.Typed.YieldBody
