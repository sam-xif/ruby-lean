import Books.TypeSoundness.Rules.Singleton.SingletonRun
import Books.TypeSoundness.Rules.Method.MethodArgs

/-! Recover own singleton dispatch from class-valued receiver conformance. The call
site is retained, and execution still consumes the entire checked parameter domain. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem declared_singleton_run {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Value} {args : List Value} {site : SendSite}
    (hm : StateOk κ Γ I m) (hv : denM (.clsOf c.name) m recv)
    (hc : c ∈ κ.classes) (hd : d ∈ c.smethods) (hn : DirectSendName d.name)
    (hp : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (hb : SemSafeCtxA (singletonBodyCtx κ c.name d.name) ps .ivar0 d.body τ
      (singletonBodyCtx κ c.name d.name) Γb .ivar0)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hw : CallWorld κ) (hk : m.kont = [])
    (hargs : DenAll (ps.map (·.2)) m args)
    (hconst : ∀ x, constGet? (singletonBodyCtx κ c.name d.name) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) :
    ∃ next, Interp.finishSend m recv site d.name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  obtain ⟨k, hnamed, _, rows⟩ := hm.classes c hc
  obtain ⟨e, md, he, _, row, hparams, hbody, hu, code⟩ := rows d hd
  have classSite := hm.classSites.at_class hc hnamed
  obtain ⟨tail, hchain⟩ := classFrontB_sound (classSite.eigen_front he)
  have hl : lookup m.heap (.ref k) d.name = some (e, md) :=
    lookup_own_first (by simpa only [classOf, he] using hchain) row code.visibilityOnly
  have hr : recv = .ref k := by cases recv <;> simp_all [denM, isClassRefNamed]
  have hp' : md.params = (ps.map (·.1)).map RubyCore.Param.req :=
    hparams.trans (by rw [hp]; exact toRubyParams_required ps)
  rw [hr]
  exact resolved_singleton_run hp' hbody hps hτ hb hm ht ha classSite he hw hk code hu hl
    (by simpa using denAll_length hargs) hargs hconst hΓ hn

#print axioms declared_singleton_run
end Checker.Soundness.Typed
