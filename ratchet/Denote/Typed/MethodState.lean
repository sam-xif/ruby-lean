import Denote.Typed.MethodReturn
import Denote.Sem.Reframe

/-! Full conformance at the ordinary-method boundary. Entry binds the body's environment;
return restores the caller's environment and frame while retaining the body's heap facts.
-/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem currentFrame_pushMethodFrame (m : Machine) (f : RubyCore.Frame) :
    (pushMethodFrame m f).currentFrame = f := by
  simp [pushMethodFrame, Machine.currentFrame, Array.getD_eq_getD_getElem?]

theorem rootFrame_eq_currentFrame {m : Machine} (h : m.stack ≠ []) :
    m.frames.getD (m.stack.headD 0) default = m.currentFrame := by
  cases hs : m.stack with
  | nil => exact False.elim (h hs)
  | cons i rest => simp [Machine.currentFrame, hs]

theorem method_enter_state {κ : Ctx} {Γ Γb : Env} {I : Ty} {m : Machine}
    {f : RubyCore.Frame} {fr : Option Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hs : f.self = m.currentFrame.self) (hb : f.blk = m.currentFrame.blk)
    (hc : f.cref = m.currentFrame.cref) (hd : f.defmod = m.currentFrame.defmod)
    (hcap : f.captured = m.currentFrame.captured)
    (hvis : κ.scope.runtimeClass ≠ none → defaultDefVis (pushMethodFrame m f) = .pub)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (he : EnvOk Γb (pushMethodFrame m f)) (hf : FrameOk fr (pushMethodFrame m f)) :
    StateOk (κ.withFrame fr) Γb I (pushMethodFrame m f) :=
  StateOk_reframe hm ht ha rfl
    (by rw [currentFrame_pushMethodFrame]; exact hs)
    (by rw [currentFrame_pushMethodFrame]; exact hb)
    (by rw [currentFrame_pushMethodFrame]; exact hc)
    (by rw [currentFrame_pushMethodFrame]; exact hd)
    (by rw [currentFrame_pushMethodFrame]; exact hcap) rfl hvis hk
    (by simp [FrameInRange, pushMethodFrame]) he hf

theorem method_pop_currentFrame {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange m) (hc : f.captured = none)
    (h : Framed (pushMethodFrame m f) n) : (popMethodFrame n).currentFrame = m.currentFrame := by
  have hp := method_pop_framed hl.2 hc h
  rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by rw [hp.stack]; exact hl.1),
    ← rootFrame_eq_currentFrame hl.1, hp.stack]
  exact method_savedFrames hc h _ hl.2

theorem method_body_scope {m n : Machine} {f : RubyCore.Frame}
    (h : Framed (pushMethodFrame m f) n) : frameScope n.currentFrame = frameScope f := by
  have hs := h.frames.scope
  rw [rootFrame_eq_currentFrame (by simp [h.stack, pushMethodFrame]),
    rootFrame_eq_currentFrame (by simp [pushMethodFrame]), currentFrame_pushMethodFrame] at hs
  exact hs

theorem method_pop_state {κ : Ctx} {Γ Γb : Env} {I : Ty} {m n : Machine}
    {f : RubyCore.Frame} {fr : Option Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hu : RootUncaptured m) (hc : f.captured = none)
    (hs : frameScope f = frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : Framed (pushMethodFrame m f) n) (hn : StateOk (κ.withFrame fr) Γb I n) :
    StateOk κ Γ I (popMethodFrame n) := by
  have hp := method_pop_framed hm.frameInRange.2 hc h
  have hpop := method_pop_currentFrame hm.frameInRange hc h
  have hscope : frameScope (popMethodFrame n).currentFrame = frameScope n.currentFrame := by
    rw [hpop]
    exact ((method_body_scope h).trans hs).symm
  have htypes : ReframeFO (κ.withFrame fr) I := {
    spine := ht.spine
    self := ht.self
    block := ht.block
    consts := fun x τ hx => ht.consts x τ (by rw [hk] at hx; exact hx)
    paths := ht.paths }
  have hframe : FrameOk κ.frame (popMethodFrame n) := by
    have hfm := hm.frame
    cases hx : κ.frame with
    | none => simpa only [FrameOk, hx, hpop] using hfm
    | some fr' =>
      change (popMethodFrame n).currentFrame.meth = fr'.methName ∧ _
      have hf' : m.currentFrame.meth = fr'.methName ∧
          isAName m.heap m.currentFrame.self fr'.recvClass = true := by
        simpa only [FrameOk, hx] using hfm
      refine ⟨by rw [hpop]; exact hf'.1, ?_⟩
      rw [hpop]
      exact hp.nominal _ _ hf'.2
  have hout := StateOk_reframe hn htypes ha (n := popMethodFrame n) (fr := κ.frame) rfl
    (congrArg FrameScope.self hscope) (congrArg FrameScope.blk hscope)
    (congrArg FrameScope.cref hscope) (congrArg FrameScope.defmod hscope)
    (congrArg FrameScope.captured hscope) rfl
    (fun hr => by simpa only [defaultDefVis, hpop] using hm.classRuntime.visibility hr)
    (fun x => (hk x).symm)
    (show FrameInRange (popMethodFrame n) from
      ⟨by rw [hp.stack]; exact hm.frameInRange.1,
       by rw [hp.stack]; exact Nat.lt_of_lt_of_le hm.frameInRange.2 hp.frames.size⟩)
    (method_pop_envOk hm.frameInRange.2 hu hc h hm.env hΓ) hframe
  exact hout

#print axioms method_enter_state
#print axioms method_pop_state

/-- A required-positional method consumes its annotated body proof, not a return-type
assertion from the certificate. Both entry and caller-restoration conformance are proved.
Dispatch/installation remain separate obligations. -/
theorem required_method_runSpec {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine}
    {md : MethodDef} {name : String} {ps : List SigParam} {args : List Value}
    {e : Ratchet.Expr} {fr : Option Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = []) (hp : md.params = (ps.map (·.1)).map RubyCore.Param.req)
    (hcap : md.capturedFrame = none) (hdecl : md.declared = []) (hbody : md.body = toRuby e)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hscope : frameScope (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args) =
      frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hframe : FrameOk fr
      (pushMethodFrame m (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args)))
    (hb : SemSafeCtxA (κ.withFrame fr) ps I e τ (κ.withFrame fr) Γb I) :
    ∃ next, Interp.enterUserMethod m m.currentFrame.self name md args none = .next next ∧
      RunSpec m next Γ τ κ I := by
  let f := requiredFrame m.currentFrame.self name md (ps.map (·.1)) args
  let entry := pushMethodFrame m f
  have he : StateOk (κ.withFrame fr) ps I entry :=
    method_enter_state hm ht ha (congrArg FrameScope.self hscope)
      (congrArg FrameScope.blk hscope) (congrArg FrameScope.cref hscope)
      (congrArg FrameScope.defmod hscope) (congrArg FrameScope.captured hscope)
      (fun _ => by simp only [defaultDefVis, currentFrame_pushMethodFrame, f, requiredFrame]; rfl) hk
      (requiredFrame_envOk m _ name md ps args hlen hargs hps) hframe
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (congrArg FrameScope.captured hscope).symm
  have hs := methodFrame_runSpec hm.frameInRange.2 (f := f) rfl hτ (hb entry he)
    (fun n v hr => method_pop_state hm ht ha hu rfl hscope hk hΓ hr.1 (hr.2.2 v rfl))
  refine ⟨_, ?_, hs⟩
  rw [enterUserMethod_required m _ name md (ps.map (·.1)) args hp hcap hdecl
    (by simpa using hlen)]
  simp only [Interp.withKont, pushK, evalFrom, f, pushMethodFrame, hkont, hbody, List.nil_append]

#print axioms required_method_runSpec
end Ratchet.Denote.Typed
