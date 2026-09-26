import Denote.Sem.Core.Reframe

/-! Captured activations retain the source heap world, self/block types and lexical
lookup. Ordinary runtime scope predicates assert captured = none and must be dropped. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

/-- The captured frame supplies the lexical receiver, implicit block and lookup scope.
Its locals, kind, return home and captured parent may differ from the active caller's. -/
structure ClosureScopeEq (m : Machine) (cl : Closure) : Prop where
  self : (m.frames.getD (cl.captured.getD 0) default).self = m.currentFrame.self
  block : (m.frames.getD (cl.captured.getD 0) default).blk = m.currentFrame.blk
  cref : (m.frames.getD (cl.captured.getD 0) default).cref = m.currentFrame.cref
  owner : (m.frames.getD (cl.captured.getD 0) default).defmod = m.currentFrame.defmod

theorem ClosureScopeEq.current {m : Machine} {cl : Closure} (hr : FrameInRange m)
    (hc : cl.captured = some (m.stack.headD 0)) : ClosureScopeEq m cl := by
  have hf : m.frames.getD (cl.captured.getD 0) default = m.currentFrame := by
    simpa only [hc, Option.getD_some] using (currentFrame_headD hr.1).symm
  exact ⟨congrArg RubyCore.Frame.self hf, congrArg RubyCore.Frame.blk hf,
    congrArg RubyCore.Frame.cref hf, congrArg RubyCore.Frame.defmod hf⟩

theorem StateOk_withoutRuntimeScope {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (h : StateOk κ Γ I m) : StateOk κ.withoutRuntimeScope Γ I m :=
  { h with
    runtime := by intro hr; cases hr
    classRuntime := by intro cn hr; cases hr
    singletonRuntime := by intro cn hr; cases hr
    classSites := h.classSites.recontext (by
      intro cn hc
      exact List.mem_append_left _ (by simpa [classSiteNames, Ctx.withoutRuntimeScope] using hc))
      (fun _ hn => hn) }

theorem ReframeFO.withoutRuntimeScope {κ : Ctx} {I : Ty} (h : ReframeFO κ I) :
    ReframeFO κ.withoutRuntimeScope I := ⟨h.spine, h.self, h.block, h.consts, h.paths⟩

/-- Full conformance at an unchanged heap and lexical scope, with an independently
proved body environment. The copied self and block keep their original types. -/
theorem StateOk_captured_reframe {κ : Ctx} {Γ Γb : Env} {I : Ty} {m n : Machine}
    (h : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hh : n.heap = m.heap) (hs : n.currentFrame.self = m.currentFrame.self)
    (hb : n.currentFrame.blk = m.currentFrame.blk)
    (hc : n.currentFrame.cref = m.currentFrame.cref)
    (hd : n.currentFrame.defmod = m.currentFrame.defmod)
    (hk : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x)
    (hr : FrameInRange n) (he : EnvOk Γb n) (hf : FrameOk none n) :
    StateOk (κ.withoutRuntimeScope.withFrame none) Γb I n :=
  StateOk_reframe_scopes (StateOk_withoutRuntimeScope h) ht.withoutRuntimeScope ha
    hh hs hb hc hd (by intro h; cases h) (by intro _ h; cases h)
    (by intro _ h; cases h) hk hr he hf

#print axioms StateOk_captured_reframe
end Ratchet.Denote
