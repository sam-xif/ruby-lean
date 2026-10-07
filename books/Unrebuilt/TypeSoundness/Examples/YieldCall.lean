import Books.TypeSoundness.Examples.YieldBody
import Books.TypeSoundness.Rules.Method.BlockEntry
import Books.TypeSoundness.Rules.Iterator.Start

/-! Rung 094's twice method from actual post-dispatch entry, with a checked callback.
The main caller survives both yields. Installation/lookup and checker admission are
separate; this example supplies neither an unproved body premise nor a return assertion. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.YieldBody
open RubyCore Checker Checker.Soundness

def method (m : Machine) : MethodDef :=
  { params := [], body := toRuby twice, owner := m.currentFrame.defmod, cref := m.currentFrame.cref }

theorem call {m : Machine} {κ : Ctx} {Γ Γb : Env} {I : Ty}
    {cl : Closure} {name : String} {names : List String} {body : Checker.Expr}
    {o : ObjId} {code : ClosureCode}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches code cl)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (hmain : closureMainB κ I = true) (hfree : nameFreeN κ "+" = true)
    (hin : activationEnvB ([(name, .int)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, .int)] ++ blockLocals cl.locals ++ Γ) I
      body .int (closureBodyCtx κ) Γb I) :
    StepSpec m Γ .int
      (Interp.enterUserMethod m m.currentFrame.self "twice" (method m) [] (some (.ref o))) κ I := by
  let f := requiredBlockFrame m.currentFrame.self "twice" (method m) [] [] (some (.ref o))
  let entry := pushMethodFrame m f
  have hactive : entry.currentFrame = f := currentFrame_pushMethodFrame m f
  have hmain' := hmain
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain'
  obtain ⟨hr, _, _, hasm, hself, hblock, hconst, hi⟩ := hmain'
  have hu : RootUncaptured m := by
    rw [RootUncaptured, rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (hm.runtime hr).captured
  have hfr := method_pop_framed hm.frameInRange.2 (f := f) rfl (Framed.refl entry)
  have hcur := method_pop_currentFrame hm.frameInRange (f := f) rfl (Framed.refl entry)
  have hs := iterator_push_caller_state hm (ReframeFO.empty hi hself hblock hconst) hasm hu f rfl
    (by
      intro p hp
      have h := List.all_eq_true.mp hin p (List.mem_append_right _ hp)
      simp only [Bool.and_eq_true] at h
      exact h.1)
  have hn : CallbackCaller κ Γ I cl [(name, .int)] names Γb entry := by
    refine ⟨hs, hc, ?_⟩
    intro x τ hx
    rw [show (popMethodFrame entry).stack = m.stack from hfr.stack]
    exact (closure_saved_bindings (Framed.refl entry).frames _ hm.frameInRange.2 x).trans (hd x τ hx)
  have hscope : CallbackMethodScope entry := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hactive]
    · rw [hcur]; rfl
    · rw [hcur]; rfl
    · rw [hcur]; rfl
    · rfl
  have hentry : StateOk (callbackMethodCtx κ ⟨"Object", "Object", "twice", false⟩ code) [] I entry := by
    apply callbackMethod_state hs hmain hscope
      (by simp [FrameInRange, pushMethodFrame])
    · constructor
      · intro x τ hx; cases hx
      · intro x _
        change Machine.getLocal.go entry x m.frames.size (entry.frames.size + 1) = .nil
        simp [Machine.getLocal.go, entry, pushMethodFrame, f, requiredBlockFrame, requiredFrame,
          Array.getD_eq_getD_getElem?]
    · simp only [FrameOk, currentFrame_pushMethodFrame]
      refine ⟨rfl, ?_, rfl⟩
      simp only [Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM]
      change isAName entry.heap m.currentFrame.self "Object" = true
      rw [(hm.runtime hr).self]
      exact (hm.runtime hr).object
    · refine ⟨.ref o, by rw [hactive]; rfl, ?_⟩
      rw [denM]
      exact ⟨cl, by simp only [procClosure?, pushMethodFrame, hproc],
        hcode, by simp [denSpineFrom], Or.inl rfl⟩
  have hrun := run hn hentry hscope
    (by change m.frames.size ≠ m.stack.headD 0; exact Nat.ne_of_gt hm.frameInRange.2)
    (by rw [hactive]; rfl) hproc hp he hmain hfree hin hout rfl hfix hb m.frames.size
  rw [enterUserMethod_required_block m m.currentFrame.self "twice" (method m) [] []
    (some (.ref o)) rfl rfl rfl rfl]
  simpa only [StepSpec, method, Interp.withKont, pushK, evalFrom, entry, f, pushMethodFrame,
    hk, List.nil_append] using hrun.rebase hfr

#print axioms call
end Checker.Soundness.Typed.YieldBody
