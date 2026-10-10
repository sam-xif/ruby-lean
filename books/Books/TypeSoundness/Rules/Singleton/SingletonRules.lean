import Books.TypeSoundness.Rules.Singleton.SingletonDefine
import Books.TypeSoundness.Rules.Singleton.SingletonExpr
import Books.TypeSoundness.Rules.Singleton.SingletonImplicit
import Books.TypeSoundness.Rules.Constructor.ConstructorImplicit
import Books.TypeSoundness.Conformance.Class.ClassGuards
import Books.TypeSoundness.Conformance.Names.NativeGuards
import Books.TypeSoundness.Checker.Guards.SingletonGuards

/-! Constructor-derived obligations for the own singleton fragment. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

-- singletonDef/callSingleton/callSingletonImplicit now live in SingletonRulesActual.

theorem SemSafeCtxA.newImplicit {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {args : List Checker.Expr}
    (hs : κ.selfTy = some (.clsOf c.name))
    (ha : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hc : c ∈ κ'.classes) (hd : d ∈ c.methods) (hn : d.name = "initialize")
    (hnew : smroGet? κ'.classes c.name "new" = none) (halloc : c.name ∈ κ'.pos.plainAlloc)
    (hp : d.params = ps.map (fun p => Checker.Param.req p.1))
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
    {c : Cls} {e : Checker.Expr}
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

#print axioms SemSafeCtxA.newImplicit
#print axioms SemSafeCtxA.instanceType
end Checker.Soundness.Typed
