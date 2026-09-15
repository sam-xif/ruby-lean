import Denote.Typed.InstanceResolvedRun
import Denote.Sem.InheritedLookup

/-! Inherited calls from declared chains and annotation-domain bodies. Conformance supplies
the receiver/owner sites and actual code; the signature is never used as its own body proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem declared_inherited_run {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {sendSite : SendSite} {receiver owner : Cls} {d : Defn} {pre post : List String}
    {recv : Value} {args : List Value} {ps : List SigParam}
    (hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (body : SemSafeCtxA (instanceBodyCtx κ ⟨receiver.name, owner.name, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ ⟨receiver.name, owner.name, d.name⟩ Ib) Γb Ib)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hrc : receiver ∈ κ.classes) (hoc : owner ∈ κ.classes) (hd : d ∈ owner.methods)
    (hchain : ancestors? κ.classes receiver.name = some (pre ++ owner.name :: post))
    (hmiss : ∀ cn ∈ pre, ∃ old ∈ κ.classes, old.name = cn ∧ d.name ∉ ownNames κ.classes cn)
    (hw : CallWorld κ) (hkont : m.kont = [])
    (hi : FirstOrder Ib = true) (hv : denM (.inst receiver.name Ib) m recv)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨receiver.name, owner.name, d.name⟩ Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none ∨ DirectSendName d.name)
    (hn : d.name ≠ "initialize")
    (hshadow : ∀ k, classNamed? m.heap owner.name = some k → Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (· != k)) d.name = none) :
    ∃ next, Interp.finishSend m recv sendSite d.name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  obtain ⟨r, recvSite⟩ := hm.classSites.of_class hrc
  obtain ⟨k, ownerSite⟩ := hm.classSites.of_class hoc
  obtain ⟨j, md, hj, hl, hparam, hbody, hu, code⟩ :=
    declared_inherited_code hm hrc recvSite.named hoc hd hchain hmiss
  have he : j = k := Option.some.inj (hj.symm.trans ownerSite.named)
  subst j
  have hnom : isExactInst m.heap recv receiver.name = true := by rw [denM] at hv; exact hv.1
  have hco := exactInst_classOf hnom recvSite.named
  have hlookup : lookup m.heap recv d.name = some (k, md) := by
    rw [lookup_eq_methodOn, hco]; exact hl
  exact resolved_instance_run (fr := ⟨receiver.name, owner.name, d.name⟩)
    (hparam.trans (by rw [hparams]; exact toRubyParams_required ps)) hbody hps hτ body
    hm ht ha recvSite ownerSite hw hkont code hu hlookup hi hv hlen hargs hk hΓ hp hn
    (hshadow k ownerSite.named)

#print axioms declared_inherited_run
end Ratchet.Denote.Typed
