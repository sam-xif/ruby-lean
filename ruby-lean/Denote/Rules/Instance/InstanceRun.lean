import Denote.Rules.Instance.InstanceResolvedRun

/-! Full class-parameterized instance calls from main or instance callers. Lookup supplies actual code;
the separately proved parameter/return annotation domain supplies the entire body contract. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem instance_method_run_at {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine} {sendSite : SendSite}
    {c : Cls} {d : Defn} {recv : Value} {args : List Value} {ps : List SigParam}
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (body : SemSafeCtxA (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hw : CallWorld κ) (hkont : m.kont = [])
    (hi : FirstOrder Ib = true) (hv : denM (.inst c.name Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none ∨ DirectSendName d.name)
    (hn : d.name ≠ "initialize") :
    ∃ next, Interp.finishSend m recv sendSite d.name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  obtain ⟨k, site⟩ := hm.classSites.of_class hc
  have hfront (j : ObjId) (hj : classNamed? m.heap c.name = some j) : classFrontB m.heap j = true := by
    have he : k = j := Option.some.inj (site.named.symm.trans hj)
    simpa only [← he] using site.front
  obtain ⟨j, md, hj, hl, paramsEq, bodyEq, hundef, code⟩ := classesOk_lookup hm.classes hc hd hv hfront
  have he : j = k := Option.some.inj (hj.symm.trans site.named)
  subst j
  have hparam : md.params = (ps.map (·.1)).map RubyCore.Param.req :=
    paramsEq.trans (by rw [hparams]; exact toRubyParams_required ps)
  have hnom : isExactInst m.heap recv c.name = true := by rw [denM] at hv; exact hv.1
  have hco := exactInst_classOf hnom site.named
  obtain ⟨rest, hrest⟩ := classFrontB_sound site.front
  exact resolved_instance_run (fr := ⟨c.name, c.name, d.name⟩) hparam bodyEq hps hτ body
    hm ht ha site site hw hkont code hundef hl hi hv hlen hargs hk hΓ hp hn
    (by simp [hco, hrest, Interp.crubyShadow]; rfl)

/-- Compatibility specialization: existing main-call users share the general proof. -/
theorem instance_method_run {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {c : Cls} {d : Defn} {recv : Value} {args : List Value} {ps : List SigParam}
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (body : SemSafeCtxA (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hr : κ.scope.runtimeMain = true) (hw : κ.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hkont : m.kont = [])
    (hi : FirstOrder Ib = true) (hv : denM (.inst c.name Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none ∨ DirectSendName d.name)
    (hn : d.name ≠ "initialize") :
    ∃ next, Interp.finishSend m recv .explicit d.name args .none = .next next ∧ RunSpec m next Γ τ κ I :=
  instance_method_run_at hparams hps hτ body hm ht ha hc hd (.main hr hw hcl) hkont hi hv hlen hargs hk hΓ hp hn

#print axioms instance_method_run_at
#print axioms instance_method_run
end Ratchet.Denote.Typed
