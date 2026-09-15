import Denote.Typed.InstanceState
import Denote.Typed.MethodChecked

/-! Recover an installed method and its persistent site from StateOk, then apply the
annotation-checked body at the actual explicit-call entry. This is the body-local contract;
caller restoration and the constructor's ordinary-payload guarantee remain separate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem checked_instance_entry {κ : Ctx} {Γ : Env} {I Ib : Ty} {m : Machine}
    {c : Cls} {d : Defn} {recv : Value} {args : List Value}
    (body : CheckedBody (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Ib d)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hr : κ.scope.runtimeMain = true ∨ κ.scope.runtimeClass ≠ none)
    (hi : FirstOrder Ib = true) (hv : denM (.inst c.name Ib) m recv)
    (hlen : args.length = body.params.length) (hargs : DenAll (body.params.map (·.2)) m args)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ x)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none) (hn : d.name ≠ "initialize") :
    ∃ n, Interp.finishSend m recv .explicit d.name args .none = .next n ∧
      n.ctl = .eval (toRuby d.body) ∧
      StateOk (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) body.params Ib n ∧
      RunSpec n (evalFrom n d.body) body.out body.ret
        (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Ib := by
  obtain ⟨k, site⟩ := hm.classSites.of_class hc
  have hfront (j : ObjId) (hj : classNamed? m.heap c.name = some j) : classFrontB m.heap j = true := by
    have he : k = j := Option.some.inj (site.named.symm.trans hj)
    simpa only [← he] using site.front
  obtain ⟨j, md, hj, hl, hparams, hbody, hu, code⟩ := classesOk_lookup hm.classes hc hd hv hfront
  have he : j = k := Option.some.inj (hj.symm.trans site.named)
  subst j
  have hphase : m.preludeMode = false := by
    rcases hr with hr | hr
    · exact (hm.runtime hr).phase
    · cases hs : κ.scope.runtimeClass with
      | none => exact False.elim (hr hs)
      | some cn => obtain ⟨_, ready⟩ := hm.classRuntime cn hs; exact ready.phase
  obtain ⟨n, hentry, hctl, hstate⟩ := instance_enterUserMethod_state hm ht ha site hphase code hi hv
    hlen hargs body.paramsFO hk (hparams.trans (checked_body_rubyParams body))
  have hnom : isExactInst m.heap recv c.name = true := by rw [denM] at hv; exact hv.1
  have hco := exactInst_classOf hnom site.named
  obtain ⟨o, rfl, _, _, _⟩ := exactInst_receiver hnom site.named
  obtain ⟨rest, hrest⟩ := classFrontB_sound site.front
  have hsend := finishSend_instance (args := args) (hp o rfl) hl hu code hn
    (by rw [hco]; exact hrest)
  exact ⟨n, hsend.trans hentry, hctl.trans (congrArg Ctl.eval hbody), hstate,
    checked_body_context body n hstate⟩

#print axioms checked_instance_entry
end Ratchet.Denote.Typed
