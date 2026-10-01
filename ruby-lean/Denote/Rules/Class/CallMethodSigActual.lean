import Denote.Rules.Instance.InstanceExpr
import Denote.Sem.Class.ClassGuards
import Denote.Sem.Names.NativeGuards

/-! The callMethodSig provider: an explicit-receiver call to a declared instance method. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.callMethodSig {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.inst c.name Ib) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes) (hd : d ∈ c.methods)
    (hn : d.name ≠ "initialize") (hname : directCallNameB d.name = true)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name, false⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name, false⟩ Ib) Γb Ib)
    (hg : instanceCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact hr.instanceCall_at ha (explicitReceiverB_sound hs) hc hd hn (directCallNameB_sound hname)
    hp hps hret hself hb (reframeTypesB_sound ht) hasms (callWorldB_sound hw)
    (fun x => (constGet?_empty (κ := instanceBodyCtx κ₂ ⟨c.name, c.name, d.name, false⟩ Ib) hco x).trans
      (constGet?_empty hco x).symm)
    (List.all_eq_true.mp hΓ)

#print axioms SemSafeCtxA.callMethodSig
end Ratchet.Denote.Typed
