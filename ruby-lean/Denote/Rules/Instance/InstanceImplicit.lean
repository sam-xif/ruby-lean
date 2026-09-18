import Denote.Rules.Instance.InstanceExpr

/-! Implicit and bare-name instance calls use the same full annotated-body contract as
explicit calls. The receiver is retained across arguments; the caller world is not fixed. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.instanceImplicit {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {args : List Ratchet.Expr}
    (hself : κ.selfTy = some (.inst c.name Ib))
    (hargs : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hc : c ∈ κ'.classes) (hd : d ∈ c.methods) (hn : d.name ≠ "initialize")
    (hname : DirectSendName d.name)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hIb : FirstOrder Ib = true)
    (hbody : SemSafeCtxA (instanceBodyCtx κ' ⟨c.name, c.name, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ' ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (ht : ReframeFO κ' I') (ha : κ'.asms = []) (hw : CallWorld κ')
    (hconst : ∀ x, constGet? (instanceBodyCtx κ' ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ' x)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send none d.name args none) τ κ' Γ' I' := by
  intro m hm
  let start := evalFrom m (.send none d.name args none)
  have hv : denM (.inst c.name Ib) start m.currentFrame.self := by
    apply (Framed_reCtl m _ []).firstOrder (.inst c.name Ib) hIb
    simpa only [SelfTyOk, hself] using hm.selfTy
  have hfinish (n : Machine) (hn' : StateOk κ' Γ' I' n) (hk : n.kont = [])
      (hv : denM (.inst c.name Ib) n m.currentFrame.self)
      (vs : List Value) (hvs : DenAll (ps.map (·.2)) n vs) :
      StepSpec n Γ' τ (Interp.finishSend n m.currentFrame.self .implicit d.name vs .none) κ' I' := by
    obtain ⟨next, hs, hr⟩ := instance_method_run_at hparams hps hτ hbody hn' ht ha hc hd hw hk
      hIb hv (by simpa using denAll_length hvs) hvs hconst hΓ (fun _ _ => Or.inr hname) hn
    rw [hs]
    exact hr
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  exact hargs.startArgsKeep (P := fun n => denM (.inst c.name Ib) n m.currentFrame.self)
    (StateOk_reCtl hm _ []) rfl [] []
    (by
      intro t ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      exact (hps p hp).1)
    trivial (fun h hv => h.firstOrder (.inst c.name Ib) hIb _ hv) hv hfinish

/-- Ruby's zero-argument bare call is a distinct dispatch site, not a missing-name leaf. -/
theorem SemSafeCtxA.instanceVcall {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty}
    {c : Cls} {d : Defn}
    (hself : κ.selfTy = some (.inst c.name Ib))
    (hc : c ∈ κ.classes) (hd : d ∈ c.methods) (hn : d.name ≠ "initialize")
    (hname : DirectSendName d.name) (hparams : d.params = [])
    (hτ : FirstOrder τ = true) (hIb : FirstOrder Ib = true)
    (hbody : SemSafeCtxA (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) [] Ib d.body τ
      (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hw : CallWorld κ)
    (hconst : ∀ x, constGet? (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.vcall d.name) τ κ Γ I := by
  intro m hm
  let start := evalFrom m (.vcall d.name)
  have hv : denM (.inst c.name Ib) start m.currentFrame.self := by
    apply (Framed_reCtl m _ []).firstOrder (.inst c.name Ib) hIb
    simpa only [SelfTyOk, hself] using hm.selfTy
  obtain ⟨next, hs, hr⟩ := instance_method_run_at (sendSite := .vcall) (ps := []) (args := []) hparams
    (by simp) hτ hbody (StateOk_reCtl hm _ []) ht ha hc hd hw rfl hIb hv rfl trivial hconst hΓ
    (fun _ _ => Or.inr hname) hn
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  change StepSpec start Γ τ (Interp.finishSend start m.currentFrame.self .vcall d.name [] .none) κ I
  change Interp.finishSend start m.currentFrame.self .vcall d.name [] .none = .next next at hs
  rw [hs]
  exact hr

#print axioms SemSafeCtxA.instanceImplicit
#print axioms SemSafeCtxA.instanceVcall
end Ratchet.Denote.Typed
