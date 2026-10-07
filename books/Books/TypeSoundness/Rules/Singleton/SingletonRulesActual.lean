import Books.TypeSoundness.Rules.Singleton.SingletonDefine
import Books.TypeSoundness.Rules.Singleton.SingletonExpr
import Books.TypeSoundness.Rules.Singleton.SingletonImplicit
import Books.TypeSoundness.Conformance.Class.ClassGuards
import Books.TypeSoundness.Conformance.Names.NativeGuards
import Checker.Guards.SingletonGuards

/-! singletonDef/callSingleton(Implicit) providers over actual def-self (install, then
the native singleton_method_added hook) and actual singleton dispatch. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem SemSafeCtxA.singletonDef {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam} (hp : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hret : FirstOrder τ = true)
    (hb : SemSafeCtxA (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name) ps .ivar0
      d.body τ (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name) Γb .ivar0)
    (hc : c ∈ κ.classes) (hg : singletonRuleB κ Γ I c d = true) :
    SemSafeCtxA κ Γ I (.defs .self' d.name d.params d.body) .sym (singletonDeclCtx κ c d) Γ I := by
  simp only [singletonRuleB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨ht, hΓ⟩, ha, hr, hs, hnew, hmiss, hquiet, hinit⟩, hhook⟩, hplain⟩, hf⟩, htab⟩ := hg
  exact SemSafeCtxA.singletonDecl hp hps hret hb hr hs hc (reframeTypesB_sound ht)
    (List.all_eq_true.mp hΓ) ha hplain hf htab hnew hmiss hquiet hinit hhook

theorem SemSafeCtxA.callSingleton {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Checker.Expr} {args : List Checker.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hc : c ∈ κ₂.classes) (hd : d ∈ c.smethods) (hn : directCallNameB d.name = true)
    (hp : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hret : FirstOrder τ = true)
    (hb : SemSafeCtxA (singletonBodyCtx κ₂ c.name d.name) ps .ivar0 d.body τ
      (singletonBodyCtx κ₂ c.name d.name) Γb .ivar0) (hg : instanceCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact hr.singletonCall ha rfl hc hd (directCallNameB_sound hn) hp hps hret hb
    (reframeTypesB_sound ht) hasms (callWorldB_sound hw)
    (fun x => (constGet?_empty (κ := singletonBodyCtx κ₂ c.name d.name) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ)

theorem SemSafeCtxA.callSingletonImplicit {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {args : List Checker.Expr} {call : Checker.Expr}
    (hshape : ImplicitCallShape call d.name args) (hself : κ.selfTy = some (.clsOf c.name))
    (hargs : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hc : c ∈ κ'.classes) (hd : d ∈ c.smethods) (hn : directCallNameB d.name = true)
    (hp : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (hb : SemSafeCtxA (singletonBodyCtx κ' c.name d.name) ps .ivar0 d.body τ
      (singletonBodyCtx κ' c.name d.name) Γb .ivar0) (hg : instanceCallB κ' Γ' I' = true) :
    SemSafeCtxA κ Γ I call τ κ' Γ' I' := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact SemSafeCtxA.singletonImplicit hshape hself hargs hc hd (directCallNameB_sound hn)
    hp hps hτ hb (reframeTypesB_sound ht) hasms (callWorldB_sound hw)
    (fun x => (constGet?_empty (κ := singletonBodyCtx κ' c.name d.name) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ)

#print axioms SemSafeCtxA.singletonDef
#print axioms SemSafeCtxA.callSingleton
#print axioms SemSafeCtxA.callSingletonImplicit
end Checker.Soundness.Typed
