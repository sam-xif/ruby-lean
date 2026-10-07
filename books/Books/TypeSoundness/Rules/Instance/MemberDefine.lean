import Books.TypeSoundness.Rules.Instance.MemberInstall

/-! Definition obligations consume the full annotated body, even when uncalled. Ordinary
members retain an open receiver shape; initialize has the allocation-anchored body contract.
These are semantic rules, not yet certificate/checker admission. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem classNamed_payload {h : Heap} {cn : String} {k : ObjId}
    (hk : classNamed? h cn = some k) : (h.classPayload? k).isSome = true := by
  unfold classNamed? at hk
  split at hk
  · split at hk
    · cases hk; assumption
    · cases hk
  · cases hk

theorem member_definition {κ : Ctx} {Γ : Env} {I : Ty} {c : Cls} {d : Defn}
    (hr : κ.scope.runtimeClass = some c.name) (hquiet : "method_added" ≠ d.name)
    (hstate : ∀ m, StateOk κ Γ I m → StateOk (instanceDeclCtx κ c d) Γ I
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body))) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I := by
  intro m hm
  obtain ⟨k, ready⟩ := hm.classRuntime c.name hr
  let md := definedMethod m d.name (toRubyParams d.params) (toRuby d.body)
  let n := installMethod m d.name (toRubyParams d.params) (toRuby d.body)
  have hn : StateOk (instanceDeclCtx κ c d) Γ I n := hstate m hm
  have hstep : Interp.stepFn (evalFrom m (.def' d.name d.params d.body)) =
      .next { n with
        ctl := .send (.ref m.currentFrame.defmod) .reflective "method_added" [.sym d.name] none [],
        kont := [.methodEditsK [] (.sym d.name)] } := by
    have hw : frozenMethodReceiver? m.heap m.currentFrame.defmod = none := by
      rw [ready.owner]; exact ready.writable
    have hd : (m.heap.classPayload? m.currentFrame.defmod).bind (·.attached) = none := by
      rw [ready.owner]; exact ready.detached
    have hs := step_def_install (m := evalFrom m (.def' d.name d.params d.body))
      rfl ready.phase hw hd
    simpa only [evalFrom, n, installMethod, definedMethod,
      show ({ m with ctl := .eval (toRuby (.def' d.name d.params d.body)), kont := [] } : Machine).currentFrame =
        m.currentFrame from currentFrame_reCtl ..,
      show sourceMethod { m with ctl := .eval (toRuby (.def' d.name d.params d.body)), kont := [] }
        (toRubyParams d.params) (toRuby d.body) =
          sourceMethod m (toRubyParams d.params) (toRuby d.body) from sourceMethod_reCtl ..] using hs
  apply RunSpec.step (answerPoint_evalFrom _ _) hstep
  apply definition_hook_runSpec hn (Framed_defineMethod m m.currentFrame.defmod d.name md)
  · change ((defineMethod m.heap m.currentFrame.defmod d.name md).classPayload?
      m.currentFrame.defmod).isSome = true
    rw [Proof.classPayload?_isSome_defineMethod, ready.owner]
    exact classNamed_payload ready.named
  · exact defHookQuiet_install hquiet (scoped_defHookQuiet ready)

theorem SemSafeCtxA.memberDecl {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam}
    (_hparams : d.params = ps.map (fun p => Checker.Param.req p.1))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (_hself : FirstOrder Ib = true)
    (_hbody : SemSafeCtxA (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name, false⟩ Ib)
      ps Ib d.body τ (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name, false⟩ Ib) Γb Ib)
    (_hinit : d.name ≠ "initialize")
    (hr : κ.scope.runtimeClass = some c.name) (hc : c ∈ κ.classes)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true) (hroot : c.name ∉ rootAncestors)
    (hf : memberFreshB κ c d = true) (htab : memberTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name)
    (hauto : autoPrivateNames.contains d.name = false)
    (hhook : classHookSelectors.contains d.name = false) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I :=
  member_definition hr hquiet (fun _ hm =>
    StateOk_install_member hm hr hc ht hΓ ha hplain hroot hf htab hnew hmiss hquiet hauto hhook)

#print axioms SemSafeCtxA.memberDecl


end Checker.Soundness.Typed
