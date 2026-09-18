import Denote.Rules.Inherited.InheritedConstructor
import Denote.Rules.Expr.Send

/-! Receiver/argument evaluation precedes inherited initializer resolution. Every body
premise is checked over its full annotation domain in that final receiver-aware context. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.constructInherited {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {receiver owner : Cls} {d : Defn} {pre post : List String}
    {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hrecv : SemSafeCtxA κ Γ I recv (.clsOf receiver.name) κ₁ Γ₁ I₁)
    (hargs : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hsite : (match toRuby recv with | .self' => .selfRecv | _ => .explicit) = SendSite.explicit)
    (hrc : receiver ∈ κ₂.classes) (hoc : owner ∈ κ₂.classes) (hd : d ∈ owner.methods)
    (hn : d.name = "initialize")
    (hchain : ancestors? κ₂.classes receiver.name = some (pre ++ owner.name :: post))
    (hmiss : ∀ cn ∈ pre, ∃ old ∈ κ₂.classes, old.name = cn ∧ d.name ∉ ownNames κ₂.classes cn)
    (hnew : smroGet? κ₂.classes receiver.name "new" = none)
    (halloc : receiver.name ∈ κ₂.pos.plainAlloc)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hbody : SemInitA (initializerBodyCtxAt κ₂ receiver.name owner.name) ps .ivar0 d.body τ
      (initializerBodyCtxAt κ₂ receiver.name owner.name) Γb Ib)
    (ht : ReframeFO κ₂ I₂) (ha : κ₂.asms = [])
    (hr : κ₂.scope.runtimeMain = true) (hw : κ₂.pos.mainWorld = true)
    (hcl : κ₂.scope.runtimeClass = none)
    (hconst : ∀ x, constGet? (initializerBodyCtxAt κ₂ receiver.name owner.name) x = constGet? κ₂ x)
    (hΓ : ∀ p ∈ Γ₂, FirstOrder (stripAlias p.2) = true) (hIb : FirstOrder Ib = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst receiver.name Ib) κ₂ Γ₂ I₂ := by
  apply hrecv.sendVia hargs hsite rfl (by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact (hps p hp).1)
  intro m hm hk recv hv args hargs
  obtain ⟨k, n, hnamed, hs, hrun⟩ := declared_inherited_constructor_run hm hrc hoc hd hn
    hchain hmiss hnew halloc hparams hps hbody ht ha hr hw hcl hconst hΓ hIb hk hargs
  have he : recv = .ref k := by cases recv <;> simp_all [denM, isClassRefNamed]
  rw [he, hs]
  exact hrun

#print axioms SemSafeCtxA.constructInherited
end Ratchet.Denote.Typed
