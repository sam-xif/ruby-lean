import Denote.Rules.Constructor.ConstructorExpr

/-! Implicit new retains class-valued self while arguments run, then uses the same checked
initializer and full caller restoration as explicit construction. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Sorbet 0.6.13405 accepts 073's implicit new and reveals T.attached_class; it rejects
wrong initializer argument types/arity (clink 184). This exact named receiver contract
covers the own singleton factory; inherited singleton bodies need their receiver/owner split. -/
theorem SemSafeCtxA.constructImplicit {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {args : List Ratchet.Expr}
    (hself : κ.selfTy = some (.clsOf c.name))
    (hargs : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hc : c ∈ κ'.classes) (hd : d ∈ c.methods) (hn : d.name = "initialize")
    (hnew : smroGet? κ'.classes c.name "new" = none) (halloc : c.name ∈ κ'.pos.plainAlloc)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hbody : SemInitA (initializerBodyCtx κ' c.name) ps .ivar0 d.body τ
      (initializerBodyCtx κ' c.name) Γb Ib)
    (ht : ReframeFO κ' I') (ha : κ'.asms = []) (hw : CallWorld κ')
    (hconst : ∀ x, constGet? (initializerBodyCtx κ' c.name) x = constGet? κ' x)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) (hIb : FirstOrder Ib = true) :
    SemSafeCtxA κ Γ I (.send none "new" args none) (.inst c.name Ib) κ' Γ' I' := by
  intro m hm
  let start := evalFrom m (.send none "new" args none)
  have hv : denM (.clsOf c.name) start m.currentFrame.self := by
    apply (Framed_reCtl m _ []).firstOrder (.clsOf c.name) rfl
    simpa only [SelfTyOk, hself] using hm.selfTy
  have hfinish (n : Machine) (hn' : StateOk κ' Γ' I' n) (hk : n.kont = [])
      (hv : denM (.clsOf c.name) n m.currentFrame.self)
      (vs : List Value) (hvs : DenAll (ps.map (·.2)) n vs) :
      StepSpec n Γ' (.inst c.name Ib)
        (Interp.finishSend n m.currentFrame.self .implicit "new" vs .none) κ' I' := by
    obtain ⟨k, next, hnamed, hs, hr⟩ := declared_constructor_run (sendSite := .implicit)
      hn' hc hd hn hnew halloc hparams hps hbody ht ha hw hconst hΓ hIb hk hvs
    have he : m.currentFrame.self = .ref k := by
      cases hrecv : m.currentFrame.self <;> simp_all [denM, isClassRefNamed]
    rw [he, hs]
    exact hr
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  exact hargs.startArgsKeep (P := fun n => denM (.clsOf c.name) n m.currentFrame.self)
    (StateOk_reCtl hm _ []) rfl [] []
    (by
      intro t ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      exact (hps p hp).1)
    trivial (fun h hv => h.firstOrder (.clsOf c.name) rfl _ hv) hv hfinish

#print axioms SemSafeCtxA.constructImplicit
end Ratchet.Denote.Typed
