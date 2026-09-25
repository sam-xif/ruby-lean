import Denote.Rules.Singleton.SingletonDefine
import Denote.Rules.Singleton.SingletonExpr
import Denote.Rules.Constructor.ConstructorImplicit
import Denote.Sem.Class.ClassGuards
import Denote.Sem.Names.NativeGuards
import Ratchet.Guards.SingletonGuards

/-! Constructor-derived obligations for the own singleton fragment. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.singletonDef {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam} (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hret : FirstOrder τ = true)
    (hb : SemSafeCtxA (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name) ps .ivar0
      d.body τ (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name) Γb .ivar0)
    (hc : c ∈ κ.classes) (hg : singletonRuleB κ Γ I c d = true) :
    SemSafeCtxA κ Γ I (.defs .self' d.name d.params d.body) .sym (singletonDeclCtx κ c d) Γ I := by
  simp only [singletonRuleB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨ht, hΓ⟩, ha, hr, hs, hnew, hmiss, hquiet, hinit⟩, hplain⟩, hf⟩, htab⟩ := hg
  exact SemSafeCtxA.singletonDecl hp hps hret hb hr hs hc (reframeTypesB_sound ht)
    (List.all_eq_true.mp hΓ) ha hplain hf htab hnew hmiss hquiet hinit

theorem SemSafeCtxA.callSingleton {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hc : c ∈ κ₂.classes) (hd : d ∈ c.smethods) (hn : directCallNameB d.name = true)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
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

theorem SemSafeCtxA.newImplicit {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {args : List Ratchet.Expr}
    (hs : κ.selfTy = some (.clsOf c.name))
    (ha : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hc : c ∈ κ'.classes) (hd : d ∈ c.methods) (hn : d.name = "initialize")
    (hnew : smroGet? κ'.classes c.name "new" = none) (halloc : c.name ∈ κ'.pos.plainAlloc)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (hout : FirstOrder Ib = true)
    (hb : SemInitA (initializerBodyCtx κ' c.name) ps .ivar0 d.body τ
      (initializerBodyCtx κ' c.name) Γb Ib) (hg : instanceCallB κ' Γ' I' = true) :
    SemSafeCtxA κ Γ I (.send none "new" args none) (.inst c.name Ib) κ' Γ' I' := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact SemSafeCtxA.constructImplicit hs ha hc hd hn hnew halloc hp hps hb
    (reframeTypesB_sound ht) hasms (callWorldB_sound hw)
    (fun x => (constGet?_empty (κ := initializerBodyCtx κ' c.name) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ) hout

theorem SemSafeCtxA.instanceType {κ κ' : Ctx} {Γ Γ' : Env} {I I' fields : Ty}
    {c : Cls} {e : Ratchet.Expr}
    (h : SemSafeCtxA κ Γ I e (.inst c.name fields) κ' Γ' I') (hc : c ∈ κ'.classes) :
    SemSafeCtxA κ Γ I e (.cls c.name) κ' Γ' I' := by
  apply h.weaken
  intro m v hm hv
  refine ⟨hm, ?_⟩
  obtain ⟨k, hk, _⟩ := hm.classes c hc
  obtain ⟨rest, hchain⟩ := classFrontB_sound (hm.classSites.at_class hc hk).front
  simp only [denM] at hv
  obtain ⟨hi, _⟩ := hv
  cases v <;> simp only [isExactInst, hk, Bool.false_eq_true] at hi
  rename_i o
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi
  have he := Option.isNone_iff_eq_none.mp hi.1.2
  simp [denM, isAName, hk, isA, classOf, he, hi.2, hchain]

#print axioms SemSafeCtxA.singletonDef
#print axioms SemSafeCtxA.callSingleton
#print axioms SemSafeCtxA.newImplicit
#print axioms SemSafeCtxA.instanceType
end Ratchet.Denote.Typed
