import Denote.Typed.InstanceCallEntry
import Denote.Typed.MainReturn

/-! Complete instance calls from the ordinary top-level caller world. The actual lookup,
annotated binding/body, and frame return are composed; constructor payload remains explicit. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem checked_instance_call_from_main {κ : Ctx} {Γ : Env} {I Ib : Ty} {m : Machine}
    {c : Cls} {d : Defn} {recv : Value} {args : List Value}
    (body : CheckedBody (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Ib d)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hr : κ.scope.runtimeMain = true) (hw : κ.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hkont : m.kont = [])
    (hi : FirstOrder Ib = true) (hv : denM (.inst c.name Ib) m recv)
    (hlen : args.length = body.params.length) (hargs : DenAll (body.params.map (·.2)) m args)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none) (hn : d.name ≠ "initialize") :
    ∃ next, Interp.finishSend m recv .explicit d.name args .none = .next next ∧
      RunSpec m next Γ body.ret κ I := by
  obtain ⟨k, site⟩ := hm.classSites.of_class hc
  have hfront (j : ObjId) (hj : classNamed? m.heap c.name = some j) : classFrontB m.heap j = true := by
    have he : k = j := Option.some.inj (site.named.symm.trans hj)
    simpa only [← he] using site.front
  obtain ⟨j, md, hj, hl, hparams, hbody, hundef, code⟩ := classesOk_lookup hm.classes hc hd hv hfront
  have he : j = k := Option.some.inj (hj.symm.trans site.named)
  subst j
  let f := requiredFrame recv d.name md (body.params.map (·.1)) args
  have hentry := instance_enter_state hm ht ha site (hm.runtime hr).phase code hi hv
    hlen hargs body.paramsFO hk
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (hm.runtime hr).captured
  have hrun := methodFrame_runSpec hm.frameInRange.2 (f := f) rfl body.returnFO
    (checked_body_context body _ hentry)
    (fun n v result => instance_pop_main_state hm ht ha hr hw hcl hu rfl hk hΓ
      result.1 (result.2.2 v rfl))
  have henter : Interp.enterUserMethod m recv d.name md args none =
      .next (pushK [.frameK m.frames.size] (evalFrom (pushMethodFrame m f) d.body)) := by
    rw [enterUserMethod_required m recv d.name md (body.params.map (·.1)) args
      (hparams.trans (checked_body_rubyParams body)) code.captured code.declared (by simpa using hlen)]
    simp only [Interp.withKont, pushK, evalFrom, f, pushMethodFrame, hkont, hbody, List.nil_append]
  have hnom : isExactInst m.heap recv c.name = true := by rw [denM] at hv; exact hv.1
  have hco := exactInst_classOf hnom site.named
  obtain ⟨o, hrecv, _, _, _⟩ := exactInst_receiver hnom site.named
  obtain ⟨rest, hrest⟩ := classFrontB_sound site.front
  have hsend := finishSend_instance (args := args) (hp o hrecv) (hrecv ▸ hl) hundef code hn
    (by rw [← hrecv, hco]; exact hrest)
  exact ⟨_, (by rw [hrecv]; exact hsend.trans (hrecv ▸ henter)), hrun⟩

#print axioms checked_instance_call_from_main
end Ratchet.Denote.Typed
