import Denote.Rules.Constructor.ConstructorResolve
import Denote.Rules.Expr.Send

/-! Initialized construction for arbitrary declared classes and annotation domains.
Receiver and arguments may change context; publication and body checks use the final one. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.construct {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hrecv : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (hargs : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hsite : (match toRuby recv with | .self' => .selfRecv | _ => .explicit) = SendSite.explicit)
    (hc : c ∈ κ₂.classes) (hd : d ∈ c.methods) (hn : d.name = "initialize")
    (hnew : smroGet? κ₂.classes c.name "new" = none) (halloc : c.name ∈ κ₂.pos.plainAlloc)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hbody : SemInitA (initializerBodyCtx κ₂ c.name) ps .ivar0 d.body τ
      (initializerBodyCtx κ₂ c.name) Γb Ib)
    (ht : ReframeFO κ₂ I₂) (ha : κ₂.asms = [])
    (hr : κ₂.scope.runtimeMain = true) (hw : κ₂.pos.mainWorld = true)
    (hcl : κ₂.scope.runtimeClass = none)
    (hconst : ∀ x, constGet? (initializerBodyCtx κ₂ c.name) x = constGet? κ₂ x)
    (hΓ : ∀ p ∈ Γ₂, FirstOrder (stripAlias p.2) = true) (hIb : FirstOrder Ib = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst c.name Ib) κ₂ Γ₂ I₂ := by
  apply hrecv.sendVia hargs hsite rfl (by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact (hps p hp).1)
  intro m hm hk recv hv args hargs
  obtain ⟨k, n, hnamed, hs, hrun⟩ := declared_constructor_run hm hc hd hn hnew halloc hparams hps
    hbody ht ha hr hw hcl hconst hΓ hIb hk hargs
  have he : recv = .ref k := by cases recv <;> simp_all [denM, isClassRefNamed]
  rw [he, hs]
  exact hrun

#print axioms SemSafeCtxA.construct
end Ratchet.Denote.Typed
