import Denote.Typed.ConstructorLookup
import Denote.Typed.ConstructorRun
import Denote.Typed.MethodArgs

/-! Any published ordinary class: recover allocation and initializer code from conformance,
then consume the body proved at its annotations. No class name, arity, or field type is fixed. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem declared_constructor_run {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {c : Cls} {d : Defn} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hn : d.name = "initialize") (hnew : smroGet? κ.classes c.name "new" = none)
    (halloc : c.name ∈ κ.pos.plainAlloc)
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hbody : SemInitA (initializerBodyCtx κ c.name) ps .ivar0 d.body τ
      (initializerBodyCtx κ c.name) Γb Ib)
    (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κ.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hconst : ∀ x, constGet? (initializerBodyCtx κ c.name) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hIb : FirstOrder Ib = true)
    (hkont : m.kont = []) (hargs : DenAll (ps.map (·.2)) m args) :
    ∃ k n, classNamed? m.heap c.name = some k ∧
      Interp.finishSend m (.ref k) .explicit "new" args .none = .next n ∧
      RunSpec m n Γ (.inst c.name Ib) κ I := by
  obtain ⟨k, md, site, dispatch, hp, hb, code, hi⟩ := declared_constructor_code hm hc hd hn hnew
  obtain ⟨j, hj, alloc⟩ := hm.allocators c.name halloc
  have he : j = k := Option.some.inj (hj.symm.trans site.named)
  subst j
  have hparam : md.params = (ps.map (·.1)).map RubyCore.Param.req :=
    hp.trans (by rw [hparams]; exact toRubyParams_required ps)
  obtain ⟨n, hs, hrun⟩ := constructor_runSpec (κb := initializerBodyCtx κ c.name)
    hm ht ha ht alloc site dispatch code hi hparam hb (by simpa using denAll_length hargs) hargs
    hps hconst hr hw hcl rfl hconst hΓ rfl hIb hkont hbody
  exact ⟨k, n, site.named, hs, hrun⟩

#print axioms declared_constructor_run
end Ratchet.Denote.Typed
