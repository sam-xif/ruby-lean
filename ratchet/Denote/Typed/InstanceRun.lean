import Denote.Typed.InstanceDispatch
import Denote.Typed.InstanceState
import Denote.Typed.MainReturn

/-! Full class-parameterized instance calls from main. Lookup supplies the actual code;
the separately proved parameter/return annotation domain supplies the entire body contract. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

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
    ∃ next, Interp.finishSend m recv .explicit d.name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  obtain ⟨k, site⟩ := hm.classSites.of_class hc
  have hfront (j : ObjId) (hj : classNamed? m.heap c.name = some j) : classFrontB m.heap j = true := by
    have he : k = j := Option.some.inj (site.named.symm.trans hj)
    simpa only [← he] using site.front
  obtain ⟨j, md, hj, hl, paramsEq, bodyEq, hundef, code⟩ := classesOk_lookup hm.classes hc hd hv hfront
  have he : j = k := Option.some.inj (hj.symm.trans site.named)
  subst j
  let f := requiredFrame recv d.name md (ps.map (·.1)) args
  have hentry := instance_enter_state hm ht ha site (hm.runtime hr).phase code hi hv hlen hargs hps hk
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (hm.runtime hr).captured
  have hrun := methodFrame_runSpec hm.frameInRange.2 (f := f) rfl hτ (body _ hentry)
    (fun n v result => instance_pop_main_state hm ht ha hr hw hcl hu rfl hk hΓ
      result.1 (result.2.2 v rfl))
  have hparam : md.params = (ps.map (·.1)).map RubyCore.Param.req :=
    paramsEq.trans (by rw [hparams]; exact toRubyParams_required ps)
  have henter : Interp.enterUserMethod m recv d.name md args none =
      .next (pushK [.frameK m.frames.size] (evalFrom (pushMethodFrame m f) d.body)) := by
    rw [enterUserMethod_required m recv d.name md (ps.map (·.1)) args
      hparam code.captured code.declared (by simpa using hlen)]
    simp only [Interp.withKont, pushK, evalFrom, f, pushMethodFrame, hkont, bodyEq, List.nil_append]
  have hnom : isExactInst m.heap recv c.name = true := by rw [denM] at hv; exact hv.1
  have hco := exactInst_classOf hnom site.named
  obtain ⟨o, hrecv, _, _, _⟩ := exactInst_receiver hnom site.named
  obtain ⟨rest, hrest⟩ := classFrontB_sound site.front
  have hsend := finishSend_instance_direct (args := args) (hp o hrecv) (hrecv ▸ hl) hundef code hn
    (by rw [← hrecv, hco]; exact hrest)
  exact ⟨_, (by rw [hrecv]; exact hsend.trans (hrecv ▸ henter)), hrun⟩

#print axioms instance_method_run
end Ratchet.Denote.Typed
