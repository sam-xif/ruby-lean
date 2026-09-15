import Denote.Typed.InstanceRun
import Denote.Typed.Send

/-! Class-parameterized receiver-bearing calls. The result type comes from the complete
annotation-domain body proof, not a method-table signature or concrete call arguments. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.instanceCall_at {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    {site : SendSite}
    (hrecv : SemSafeCtxA κ Γ I recv (.inst c.name Ib) κ₁ Γ₁ I₁)
    (hargs : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hsite : (match toRuby recv with | .self' => .selfRecv | _ => .explicit) = site)
    (hc : c ∈ κ₂.classes) (hd : d ∈ c.methods) (hn : d.name ≠ "initialize")
    (hname : DirectSendName d.name)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hIb : FirstOrder Ib = true)
    (hbody : SemSafeCtxA (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (ht : ReframeFO κ₂ I₂) (ha : κ₂.asms = [])
    (hw : CallWorld κ₂)
    (hconst : ∀ x, constGet? (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ₂ x)
    (hΓ : ∀ p ∈ Γ₂, FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ := by
  apply hrecv.sendVia hargs hsite hIb (by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact (hps p hp).1)
  intro m hm hk recv hv args hargs
  obtain ⟨n, hs, hrun⟩ := instance_method_run_at hparams hps hτ hbody hm ht ha hc hd hw hk
    hIb hv (by simpa using denAll_length hargs) hargs hconst hΓ (fun _ _ => Or.inr hname) hn
  rw [hs]
  exact hrun

/-- Existing main-only callers use the same generic call proof. -/
theorem SemSafeCtxA.instanceCall {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hrecv : SemSafeCtxA κ Γ I recv (.inst c.name Ib) κ₁ Γ₁ I₁)
    (hargs : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hsite : (match toRuby recv with | .self' => .selfRecv | _ => .explicit) = SendSite.explicit)
    (hc : c ∈ κ₂.classes) (hd : d ∈ c.methods) (hn : d.name ≠ "initialize")
    (hname : DirectSendName d.name)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hIb : FirstOrder Ib = true)
    (hbody : SemSafeCtxA (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (ht : ReframeFO κ₂ I₂) (ha : κ₂.asms = [])
    (hr : κ₂.scope.runtimeMain = true) (hw : κ₂.pos.mainWorld = true)
    (hcl : κ₂.scope.runtimeClass = none)
    (hconst : ∀ x, constGet? (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ₂ x)
    (hΓ : ∀ p ∈ Γ₂, FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ :=
  hrecv.instanceCall_at hargs hsite hc hd hn hname hparams hps hτ hIb hbody ht ha
    (.main hr hw hcl) hconst hΓ

#print axioms SemSafeCtxA.instanceCall_at
#print axioms SemSafeCtxA.instanceCall
end Ratchet.Denote.Typed
