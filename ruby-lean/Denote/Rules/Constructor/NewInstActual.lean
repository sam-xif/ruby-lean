import Denote.Rules.Constructor.ConstructorExpr
import Denote.Rules.Init.InitRules
import Denote.Rules.Init.InitDefine
import Denote.Sem.Class.ClassGuards

/-! initDef/newInst providers: initializer definition and actual Class#new construction
(callConstruct, then reflective initialize). The body proof is consumed at construction. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.initDef {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam} (hn : d.name = "initialize")
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hout : FirstOrder Ib = true)
    (hb : SemInitA (initializerBodyCtx (instanceDeclCtx κ c d) c.name) ps .ivar0 d.body τ
      (initializerBodyCtx (instanceDeclCtx κ c d) c.name) Γb Ib)
    (hc : c ∈ κ.classes) (hg : memberRuleB κ Γ I c d = true) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I := by
  simp only [memberRuleB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨ht, hΓ⟩, ha, hr, hroot, _, _, _⟩, hplain⟩, hf⟩, htab⟩, _⟩, _⟩ := hg
  exact SemSafeCtxA.initializerDecl hn hp hps hret hout hb hr hc (reframeTypesB_sound ht)
    (List.all_eq_true.mp hΓ) ha hplain hroot hf htab

theorem SemSafeCtxA.newInst {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes) (hd : d ∈ c.methods)
    (hn : d.name = "initialize") (hnew : smroGet? κ₂.classes c.name "new" = none)
    (halloc : c.name ∈ κ₂.pos.plainAlloc)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (hout : FirstOrder Ib = true)
    (hb : SemInitA (initializerBodyCtx κ₂ c.name) ps .ivar0 d.body τ
      (initializerBodyCtx κ₂ c.name) Γb Ib)
    (hg : mainCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst c.name Ib) κ₂ Γ₂ I₂ := by
  simp only [mainCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨ht, hΓ⟩, hasms, hmain, hw, hcl, hco⟩ := hg
  exact hr.construct ha (explicitReceiverB_sound hs) hc hd hn hnew halloc hp hps hb
    (reframeTypesB_sound ht) hasms (.main hmain hw hcl)
    (fun x => (constGet?_empty (κ := initializerBodyCtx κ₂ c.name) hco x).trans
      (constGet?_empty hco x).symm)
    (List.all_eq_true.mp hΓ) hout

#print axioms SemSafeCtxA.initDef
#print axioms SemSafeCtxA.newInst
end Ratchet.Denote.Typed
