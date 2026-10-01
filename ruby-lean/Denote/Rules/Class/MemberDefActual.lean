import Denote.Rules.Instance.MemberDefine
import Denote.Sem.Class.ClassGuards

/-! The memberDef provider: a class-body def composed with its real method_added callback. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.memberDef {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam}
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name, false⟩ Ib)
      ps Ib d.body τ (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name, false⟩ Ib) Γb Ib)
    (hn : d.name ≠ "initialize") (hc : c ∈ κ.classes)
    (hg : memberRuleB κ Γ I c d = true) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I := by
  simp only [memberRuleB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨ht, hΓ⟩, ha, hr, hroot, hnew, hmiss, hquiet⟩, hplain⟩, hf⟩, htab⟩, hauto⟩,
    hhook⟩ := hg
  exact SemSafeCtxA.memberDecl hp hps hret hself hb hn hr hc (reframeTypesB_sound ht)
    (List.all_eq_true.mp hΓ) ha hplain hroot hf htab hnew hmiss hquiet hauto hhook

#print axioms SemSafeCtxA.memberDef
end Ratchet.Denote.Typed
