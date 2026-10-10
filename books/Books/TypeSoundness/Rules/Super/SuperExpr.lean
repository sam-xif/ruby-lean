import Books.TypeSoundness.Rules.Super.SuperArgs
import Books.TypeSoundness.Checker.Guards.SuperInit
import Books.TypeSoundness.Conformance.Class.ClassGuards

/-! Explicit super expressions compose argument effects with the full annotated parent
body. The lexical owner changes only during the parent activation. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem SemInitA.superInit {κ : Ctx} {Γ Γa Γb : Env} {I Ia Ib τ : Ty}
    {es : List Checker.Expr} {c : Cls} {current owner : String} {d : Defn} {ps : List SigParam}
    (ha : SemInitAllA κ Γ I es (ps.map (·.2)) κ Γa Ia)
    (hb : SemInitA (initializerBodyCtxAt κ c.name owner) ps Ia d.body τ
      (initializerBodyCtxAt κ c.name owner) Γb Ib)
    (hc : c ∈ κ.classes) (route : SuperRoute κ.classes c.name current owner d)
    (hg : superInitB κ Γa Ia Ib c current d ps τ = true) :
    SemInitA κ Γ I (.super' es none) τ κ Γa Ib := by
  have ready := superInitB_sound hg
  intro anchor m hm
  let start := evalFrom m (.super' es none)
  have hblk : Interp.methodBlk start = none := by
    change Interp.methodBlk m = none
    have hf := hm.typed.frame
    simp only [FrameOk, ready.frame] at hf
    have hk : m.currentFrame.kind ≠ .block := by rw [hf.2.2]; decide
    simp only [Interp.methodBlk, methodFrame_current hm.typed.frameInRange.1 hk]
    simpa only [BlockTyOk, ready.block] using hm.typed.blockTy
  obtain ⟨next, hs, hr⟩ := ha.startSuperArgs (hm.reCtl _ _) (m := start) rfl [] []
    (by simp) trivial (fun n hn hk vs hvs =>
      declared_super_initializer_runSpec (κb := initializerBodyCtxAt κ c.name owner)
        hn (reframeTypesB_sound ready.input) ready.asms
        (reframeTypesB_sound ready.output) hc ready.frame ready.scope ready.main ready.self
        ready.block ready.closed rfl ready.name route ready.params
        (by simpa using denAll_length hvs) hvs ready.paramsFO
        (fun x => (constGet?_empty (κ := initializerBodyCtxAt κ c.name owner) ready.consts x).trans
          (constGet?_empty ready.consts x).symm) rfl ready.current
        (List.mem_map.mpr ⟨c, hc, rfl⟩)
        (fun x => (constGet?_empty (κ := initializerBodyCtxAt κ c.name owner) ready.consts x).trans
          (constGet?_empty ready.consts x).symm) ready.locals ready.ret hk hb)
  apply InitRunSpec.step (answerPoint_evalFrom _ _) (show Interp.stepFn start = .next next from ?_)
    (hr.rebase ((InitFrame.refl hm.growth).reCtl _ _))
  change Interp.startSuperArgs start [] (toRubyList es) (Interp.methodBlk start) = .next next
  rw [hblk]
  exact hs

#print axioms SemInitA.superInit
end Checker.Soundness.Typed
