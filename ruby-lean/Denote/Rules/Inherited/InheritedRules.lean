import Denote.Rules.Inherited.InheritedConstructorExpr
import Denote.Rules.Inherited.InheritedRun
import Denote.Sem.Names.NativePrefix
import Denote.Sem.Class.ClassGuards
import Ratchet.Guards.MemberRoute

/-! Inherited call forms with only checked routes, static guards and full body premises.
Every receiver, owner, body, annotation and context is a parameter. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.newInherited {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {owner : String} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes)
    (route : MemberRoute κ₂.classes c.name owner d)
    (hn : d.name = "initialize") (hnew : smroGet? κ₂.classes c.name "new" = none)
    (halloc : c.name ∈ κ₂.pos.plainAlloc)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (hout : FirstOrder Ib = true)
    (hb : SemInitA (initializerBodyCtxAt κ₂ c.name owner) ps .ivar0 d.body τ
      (initializerBodyCtxAt κ₂ c.name owner) Γb Ib)
    (hg : mainCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst c.name Ib) κ₂ Γ₂ I₂ := by
  simp only [mainCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨ht, hΓ⟩, hasms, hmain, hw, hcl, hco⟩ := hg
  exact hr.constructInherited ha (explicitReceiverB_sound hs) hc route.member route.installed hn
    route.chain route.clear hnew halloc hp hps (by simpa only [route.nameOk] using hb)
    (reframeTypesB_sound ht) hasms hmain hw hcl
    (fun x => (constGet?_empty (κ := initializerBodyCtxAt κ₂ c.name route.cls.name) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ) hout

theorem SemSafeCtxA.callInherited {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {owner : String} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.inst c.name Ib) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes)
    (route : MemberRoute κ₂.classes c.name owner d)
    (hn : d.name ≠ "initialize") (hname : directCallNameB d.name = true)
    (hnative : nativeInstanceFreeB d.name = true)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx κ₂ ⟨c.name, owner, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ₂ ⟨c.name, owner, d.name⟩ Ib) Γb Ib)
    (hg : instanceCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  apply hr.sendVia ha (explicitReceiverB_sound hs) hself (by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact (hps p hp).1)
  intro m hm hk recv hv args hargs
  obtain ⟨n, hs, hrun⟩ := declared_inherited_run hp hps hret
    (by simpa only [route.nameOk] using hb) hm (reframeTypesB_sound ht) hasms hc
    route.member route.installed route.chain route.clear (callWorldB_sound hw) hk hself hv
    (by simpa using denAll_length hargs) hargs
    (fun x => (constGet?_empty (κ := instanceBodyCtx κ₂ ⟨c.name, route.cls.name, d.name⟩ Ib) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ)
    (fun _ _ => Or.inr (directCallNameB_sound hname)) hn (fun _ _ => nativeInstanceFreeB_shadow hnative)
  rw [hs]
  exact hrun

#print axioms SemSafeCtxA.newInherited
#print axioms SemSafeCtxA.callInherited
end Ratchet.Denote.Typed
