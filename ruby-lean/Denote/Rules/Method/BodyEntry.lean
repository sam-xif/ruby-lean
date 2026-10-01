import Denote.Rules.Method.BodyContext
import Denote.Rules.Method.BlockEntry
import Denote.Rules.Iterator.Start

/-! Ordinary zero-positional method entry for any certified callback-capable body.
Lookup/installation remain separate. The actual method frame keeps blk and callBlk. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem MethodActivation.enterBindings {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {m : Machine} {cl : Closure} {o : ObjId}
    (hm : StateOk κ Γ I m) (name : String) (md : MethodDef)
    (names : List String) (args : List Value)
    (henv : EnvOk Γm (pushMethodFrame m
      (requiredBlockFrame m.currentFrame.self name md names args (some (.ref o)))))
    (howner : md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none)
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl) :
    MethodActivation cb ⟨"Object", "Object", name, false⟩ Γm m
      (pushMethodFrame m (requiredBlockFrame m.currentFrame.self name md names args (some (.ref o)))) := by
  let f := requiredBlockFrame m.currentFrame.self name md names args (some (.ref o))
  let entry := pushMethodFrame m f
  have hactive : entry.currentFrame = f := currentFrame_pushMethodFrame m f
  have hcap : f.captured = none := rfl
  have hmain := cb.main
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, _, _, hasm, hself, hblock, hconst, hi⟩ := hmain
  have hu : RootUncaptured m := by
    rw [RootUncaptured, rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (hm.runtime hr).captured
  have hf := method_pop_framed hm.frameInRange.2 hcap (Framed.refl entry)
  have hcur := method_pop_currentFrame hm.frameInRange hcap (Framed.refl entry)
  have hcaller := iterator_push_caller_state hm (ReframeFO.empty hi hself hblock hconst) hasm hu f hcap
    (by
      intro p hp
      have h := List.all_eq_true.mp cb.inputTypes p (List.mem_append_right _ hp)
      simp only [Bool.and_eq_true] at h
      exact h.1)
  have hs : CallbackMethodScope entry := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hactive]
    · rw [hcur]; rfl
    · rw [hcur]; exact hcref
    · rw [hcur]; exact howner
    · exact hcap
  refine ⟨hm, ?_, hs, Nat.le_refl _, hf, ?_⟩
  · apply callbackMethod_state hcaller cb.main hs (by simp [FrameInRange, pushMethodFrame])
    · exact henv
    · simp only [FrameOk, currentFrame_pushMethodFrame]
      refine ⟨by simp only [f, requiredBlockFrame, requiredFrame, hsuper, Option.getD_none], ?_, rfl⟩
      simp only [Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM]
      change isAName entry.heap m.currentFrame.self "Object" = true
      rw [(hm.runtime hr).self]
      exact (hm.runtime hr).object
    · refine ⟨.ref o, by rw [hactive]; rfl, ?_⟩
      rw [denM]
      exact ⟨cl, by simp only [procClosure?, pushMethodFrame, hproc],
        hcode, by simp [denSpineFrom], Or.inl rfl⟩
  · refine ⟨o, cl, by rw [hactive]; rfl, hproc, hcode, hcaller, hc, ?_⟩
    intro x τ hx
    rw [show (popMethodFrame entry).stack = m.stack from hf.stack]
    exact (closure_saved_bindings (Framed.refl entry).frames _ hm.frameInRange.2 x).trans (hd x τ hx)

theorem MethodActivation.enter0 {κ : Ctx} {Γ : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {m : Machine} {cl : Closure} {o : ObjId}
    (hm : StateOk κ Γ I m) (name : String) (md : MethodDef)
    (howner : md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none)
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl) :
    MethodActivation cb ⟨"Object", "Object", name, false⟩ [] m
      (pushMethodFrame m (requiredBlockFrame m.currentFrame.self name md [] [] (some (.ref o)))) := by
  apply MethodActivation.enterBindings hm name md [] [] ?_ howner hcref hsuper hc hd hproc hcode
  constructor
  · intro x τ hx; cases hx
  · intro x _
    simp [Machine.getLocal, Machine.getLocal.go, pushMethodFrame, requiredBlockFrame,
      requiredFrame, Array.getD_eq_getD_getElem?]

theorem SemMethod.call0 {κ : Ctx} {Γ Γm : Env} {I τ : Ty} {cb : CheckedCallback κ Γ I}
    {m : Machine} {cl : Closure} {o : ObjId} {e : Ratchet.Expr} {name : String} {md : MethodDef}
    (hbody : SemMethod cb ⟨"Object", "Object", name, false⟩ [] e τ Γm)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (ht : FirstOrder τ = true)
    (hp : md.params = []) (he : md.body = toRuby e)
    (howner : md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none) (hcapture : md.capturedFrame = none) (hdeclared : md.declared = [])
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl) :
    StepSpec m Γ τ (Interp.enterUserMethod m m.currentFrame.self name md [] (some (.ref o))) κ I := by
  rw [enterUserMethod_required_block m _ name md [] [] _ hp hcapture hdeclared rfl]
  have hentry := MethodActivation.enter0 (cb := cb) hm name md howner hcref hsuper hc hd hproc hcode
  simpa only [StepSpec, Interp.withKont, pushK, evalFrom, pushMethodFrame, hk, he, List.nil_append]
    using hbody.methodReturn ht hentry m.frames.size

#print axioms MethodActivation.enterBindings
#print axioms MethodActivation.enter0
#print axioms SemMethod.call0
end Ratchet.Denote.Typed
