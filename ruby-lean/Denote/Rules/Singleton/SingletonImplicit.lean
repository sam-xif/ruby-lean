import Denote.Rules.Singleton.SingletonLookupRun
import Ratchet.Guards.ImplicitCall

/-! Bare and parenthesized implicit singleton calls retain the real receiver across
arguments, dispatch at their own call site, and restore the full caller state. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.singletonImplicit {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {args : List Ratchet.Expr} {call : Ratchet.Expr}
    (hshape : ImplicitCallShape call d.name args)
    (hself : κ.selfTy = some (.clsOf c.name))
    (hargs : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hc : c ∈ κ'.classes) (hd : d ∈ c.smethods) (hn : DirectSendName d.name)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (hb : SemSafeCtxA (singletonBodyCtx κ' c.name d.name) ps .ivar0 d.body τ
      (singletonBodyCtx κ' c.name d.name) Γb .ivar0)
    (ht : ReframeFO κ' I') (ha : κ'.asms = []) (hw : CallWorld κ')
    (hconst : ∀ x, constGet? (singletonBodyCtx κ' c.name d.name) x = constGet? κ' x)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I call τ κ' Γ' I' := by
  intro m hm
  let start := evalFrom m call
  let site : SendSite := match call with | .vcall _ => .vcall | _ => .implicit
  have hv : denM (.clsOf c.name) start m.currentFrame.self := by
    apply (Framed_reCtl m _ []).firstOrder (.clsOf c.name) rfl
    simpa only [SelfTyOk, hself] using hm.selfTy
  have hfinish (n : Machine) (hn' : StateOk κ' Γ' I' n) (hk : n.kont = [])
      (hv : denM (.clsOf c.name) n m.currentFrame.self)
      (vs : List Value) (hvs : DenAll (ps.map (·.2)) n vs) :
      StepSpec n Γ' τ (Interp.finishSend n m.currentFrame.self site d.name vs .none) κ' I' := by
    obtain ⟨next, hs, hr⟩ := declared_singleton_run hn' hv hc hd hn hp hps hτ hb
      ht ha hw hk hvs hconst hΓ
    rw [hs]
    exact hr
  have hstep : Interp.stepFn start =
      Interp.startArgs start m.currentFrame.self site d.name [] (toRubyList args) .none := by
    cases hshape <;> rfl
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  rw [hstep]
  exact hargs.startArgsKeep (P := fun n => denM (.clsOf c.name) n m.currentFrame.self)
    (StateOk_reCtl hm _ []) rfl [] []
    (by intro t ht; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht; exact (hps p hp).1)
    trivial (fun h hv => h.firstOrder (.clsOf c.name) rfl _ hv) hv hfinish

#print axioms SemSafeCtxA.singletonImplicit
end Ratchet.Denote.Typed
