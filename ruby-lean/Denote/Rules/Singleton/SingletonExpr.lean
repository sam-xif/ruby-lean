import Denote.Rules.Singleton.SingletonLookupRun
import Denote.Rules.Expr.Send

/-! Own singleton calls recover exact executed code from conformance and check the body
at its full parameter domain. Inherited singleton lookup is a separate obligation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Sorbet's own singleton calls use the declared argument/result domain: 073 is accepted,
while Point.origin(1) is rejected (clink 177). Executed code and a body proof justify it here. -/
theorem SemSafeCtxA.singletonCall {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    {site : SendSite}
    (hrecv : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (hargs : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hsite : (match toRuby recv with | .self' => .selfRecv | _ => .explicit) = site)
    (hc : c ∈ κ₂.classes) (hd : d ∈ c.smethods) (hname : DirectSendName d.name)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (singletonBodyCtx κ₂ c.name d.name) ps .ivar0 d.body τ
      (singletonBodyCtx κ₂ c.name d.name) Γb .ivar0)
    (ht : ReframeFO κ₂ I₂) (ha : κ₂.asms = []) (hw : CallWorld κ₂)
    (hconst : ∀ x, constGet? (singletonBodyCtx κ₂ c.name d.name) x = constGet? κ₂ x)
    (hΓ : ∀ p ∈ Γ₂, FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ := by
  apply hrecv.sendVia hargs hsite rfl (by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact (hps p hp).1)
  intro m hm hk recv hv args hargs
  obtain ⟨next, hs, hr⟩ := declared_singleton_run hm hv hc hd hname hparams hps hτ hbody
    ht ha hw hk hargs hconst hΓ
  rw [hs]
  exact hr

#print axioms SemSafeCtxA.singletonCall
end Ratchet.Denote.Typed
