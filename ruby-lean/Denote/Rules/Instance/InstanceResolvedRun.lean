import Denote.Rules.Instance.InstanceDispatch
import Denote.Rules.Instance.InstanceState
import Denote.Rules.Instance.CallWorld

/-! A fully resolved ordinary method call with independent receiver and lexical owner.
Lookup and the native prefix are obligations, never inferred from an ancestor's signature.
The complete annotated body executes at that receiver/owner context before caller return. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem resolved_instance_run {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {site : SendSite} {fr : Ratchet.Frame} {r k : ObjId} {md : MethodDef} {e : Ratchet.Expr}
    {recv : Value} {args : List Value} {ps : List SigParam}
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req) (hbody : md.body = toRuby e)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (body : SemSafeCtxA (instanceBodyCtx κ fr Ib) ps Ib e τ (instanceBodyCtx κ fr Ib) Γb Ib)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (recvSite : InstanceSite κ fr.recvClass r m.heap) (ownerSite : InstanceSite κ fr.defClass k m.heap)
    (hw : CallWorld κ) (hkont : m.kont = [])
    (code : InstanceMethodCode k fr.methName md) (hu : md.undefined = false)
    (hl : lookup m.heap recv fr.methName = some (k, md))
    (hi : FirstOrder Ib = true) (hv : denM (.inst fr.recvClass Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hk : ∀ x, constGet? (instanceBodyCtx κ fr Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none ∨ DirectSendName fr.methName)
    (hn : fr.methName ≠ "initialize")
    (hshadow : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (· != k)) fr.methName = none) :
    ∃ next, Interp.finishSend m recv site fr.methName args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  let f := requiredFrame recv fr.methName md (ps.map (·.1)) args
  have hentry := instance_enter_state_at hm ht ha recvSite ownerSite (call_world_phase hm hw)
    code hi hv hlen hargs hps hk
  have hrun := methodFrame_runSpec hm.frameInRange.2 (f := f) rfl hτ (body _ hentry)
    (fun n v result => call_world_pop_state hm ht ha hw rfl hk hΓ
      result.1 (result.2.2 v rfl))
  have henter : Interp.enterUserMethod m recv fr.methName md args none =
      .next (pushK [.frameK m.frames.size] (evalFrom (pushMethodFrame m f) e)) := by
    rw [enterUserMethod_required m recv fr.methName md (ps.map (·.1)) args
      hparams code.captured code.declared (by simpa using hlen)]
    simp only [Interp.withKont, pushK, evalFrom, f, pushMethodFrame, hkont, hbody, List.nil_append]
  have hnom : isExactInst m.heap recv fr.recvClass = true := by rw [denM] at hv; exact hv.1
  obtain ⟨o, hrecv, _, _, _⟩ := exactInst_receiver hnom recvSite.named
  have hsend := finishSend_instance_resolved (site := site) (args := args) (hp o hrecv)
    (hrecv ▸ hl) hu code hn (hrecv ▸ hshadow)
  exact ⟨_, (by rw [hrecv]; exact hsend.trans (hrecv ▸ henter)), hrun⟩

#print axioms resolved_instance_run
end Ratchet.Denote.Typed
