import Denote.Rules.Closure.Literal

/-! Execute a literal/assignment prefix without forgetting the allocated descriptor's
capture identity. The continuation is proved at the actual resulting machine. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem closure_store_seq_runSpec {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty}
    {m : Machine} (hm : StateOk κ Γ I m) (code : ClosureCode) (name : String)
    (hf : nameFreeN κ (if code.lam then "lambda" else "proc") = true) (tail : Ratchet.Expr)
    (hb : let n := (reifiedMachine m (toRubyParams code.params) code.locals
        (toRuby code.body) code.lam).setLocal name (.ref m.heap.objs.size)
      RunSpec n (evalFrom n tail) Γ' τ κ' I') :
    RunSpec m (evalFrom m (.seq [
      .vasgn .lvar name (.send none (if code.lam then "lambda" else "proc") []
        (some (.block code.params code.locals code.body))), tail])) Γ' τ κ' I' := by
  let lit := Ratchet.Expr.send none (if code.lam then "lambda" else "proc") []
    (some (.block code.params code.locals code.body))
  let fresh := reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam
  let assigned := fresh.setLocal name (.ref m.heap.objs.size)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.seqK [toRuby tail]] (evalFrom m (.vasgn .lvar name lit))) from rfl)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.asgnK .lvar name, .seqK [toRuby tail]] (evalFrom m lit)) from rfl)
  have hk : RubyCore.Proof.CatchFree [.asgnK .lvar name, .seqK [toRuby tail]] := by
    intro k hk tag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp
  apply RunSpec.step (by rfl) (RubyCore.Proof.stepFn_frame _ hk _ _
    (Or.inr ⟨_, rfl⟩) (closure_literal_step hm code.lam hf code.params code.locals code.body))
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (deliverA (.val (.ref m.heap.objs.size)) assigned [.seqK [toRuby tail]]) from by
      change StepResult.next (Interp.withCtl ((reCtl fresh (.value (.ref m.heap.objs.size))
        [.seqK [toRuby tail]]).setLocal name (.ref m.heap.objs.size)) _) = _
      rw [setLocal_reCtl]
      rfl)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.seqK []] (evalFrom assigned tail)) from rfl)
  apply RunSpec.rebase (middle := assigned) ?_
    ((Framed.of_ext (reified_ext hm _ _ _ _)).trans (Framed_setLocal fresh name _))
  apply hb.bindSpec (by
    intro k hk
    simp only [List.mem_singleton] at hk
    subst hk
    rfl)
  intro a n hr
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next (deliverA a n []) from by
    cases a with
    | val v => rfl
    | esc j => cases j <;> rfl)
  exact RunSpec.answer hr

#print axioms closure_store_seq_runSpec
end Ratchet.Denote.Typed
