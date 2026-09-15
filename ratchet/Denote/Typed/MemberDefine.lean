import Denote.Typed.MemberInstall
import Denote.Typed.InitRun

/-! Definition obligations consume the full annotated body, even when uncalled. Ordinary
members retain an open receiver shape; initialize has the allocation-anchored body contract.
These are semantic rules, not yet certificate/checker admission. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem member_definition {κ : Ctx} {Γ : Env} {I : Ty} {c : Cls} {d : Defn}
    (hr : κ.scope.runtimeClass = some c.name) (hquiet : "method_added" ≠ d.name)
    (hstate : ∀ m, StateOk κ Γ I m → StateOk (instanceDeclCtx κ c d) Γ I
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body))) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  obtain ⟨k, ready⟩ := hm.classRuntime c.name hr
  let n := installMethod m d.name (toRubyParams d.params) (toRuby d.body)
  have hs := step_def_install (m := evalFrom m (.def' d.name d.params d.body))
    rfl (defHookQuiet_install hquiet (scoped_defHookQuiet (m := m) ready))
  refine ⟨n, .sym d.name, ?_, Framed_defineMethod m m.currentFrame.defmod d.name
    (definedMethod m d.name (toRubyParams d.params) (toRuby d.body)),
    by simp [AnsOk, denM, isSymV], fun _ _ => hstate m hm⟩
  simpa only [n, installMethod, evalFrom, toRuby, deliverA, Interp.withCtl,
    reCtl, definedMethod, Machine.currentFrame, Answer.ctl] using hs

theorem SemSafeCtxA.memberDecl {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam}
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (_hself : FirstOrder Ib = true)
    (_hbody : SemSafeCtxA (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name⟩ Ib)
      ps Ib d.body τ (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (_hinit : d.name ≠ "initialize")
    (hr : κ.scope.runtimeClass = some c.name) (hc : c ∈ κ.classes)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true) (hroot : c.name ∉ rootAncestors)
    (hf : memberFreshB κ c d = true) (htab : memberTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I :=
  member_definition hr hquiet (fun _ hm =>
    StateOk_install_member hm hr hc ht hΓ ha hplain hroot hf htab hnew hmiss hquiet)

theorem SemSafeCtxA.initializerDecl {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam} (hinit : d.name = "initialize")
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (_hout : FirstOrder Ib = true)
    (_hbody : SemInitA (initializerBodyCtx (instanceDeclCtx κ c d) c.name) ps .ivar0 d.body τ
      (initializerBodyCtx (instanceDeclCtx κ c d) c.name) Γb Ib)
    (hr : κ.scope.runtimeClass = some c.name) (hc : c ∈ κ.classes)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true) (hroot : c.name ∉ rootAncestors)
    (hf : memberFreshB κ c d = true) (htab : memberTableFrameB κ.classes c d = true) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I :=
  member_definition hr (by rw [hinit]; decide) (fun _ hm =>
    StateOk_install_member hm hr hc ht hΓ ha hplain hroot hf htab
      (by rw [hinit]; decide) (by rw [hinit]; decide) (by rw [hinit]; decide))

#print axioms SemSafeCtxA.memberDecl
#print axioms SemSafeCtxA.initializerDecl
end Ratchet.Denote.Typed
