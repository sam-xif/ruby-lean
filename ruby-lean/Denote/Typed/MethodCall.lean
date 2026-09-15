import Denote.Typed.MethodArgs
import Denote.Typed.MethodResolve

/-! The ordinary call rule's semantic obligation: argument evaluation, installed lookup,
annotation-checked body, and caller restoration, on the full answer-typed contract. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.callSig {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ : Ty}
    {decl : Defn} {ps : List SigParam} {args : List Ratchet.Expr}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ'.withFrame (some ⟨"Object", "Object", decl.name⟩)) ps I' decl.body τ
      (κ'.withFrame (some ⟨"Object", "Object", decl.name⟩)) Γb I')
    (hargs : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hd : decl ∈ κ'.defs)
    (hstart : κ.scope.runtimeMain = true) (hruntime : κ'.scope.runtimeMain = true)
    (hself : κ'.selfTy = none) (hblock : κ'.blockTy = none) (hconst : κ'.consts = [])
    (hasms : κ'.asms = []) (hI : FirstOrder I' = true)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send none decl.name args none) τ κ' Γ' I' := by
  intro m hm
  let start := evalFrom m (.send none decl.name args none)
  have hfinish (n : Machine) (hn : StateOk κ' Γ' I' n) (hk : n.kont = [])
      (vs : List Value) (hv : DenAll (ps.map (·.2)) n vs) :
      StepSpec n Γ' τ (Interp.finishSend n (.ref Boot.mainId) .implicit decl.name vs .none) κ' I' := by
    obtain ⟨next, hs, hr⟩ := top_method_runSpec hparams hps hτ hbody hn hd
      (ReframeFO.empty hI hself hblock hconst) hasms hconst hΓ hk
      (by simpa using denAll_length hv) hv hruntime hblock
    rw [(hn.runtime hruntime).self] at hs
    rw [hs]
    exact hr
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  have hh := hargs.startArgs (m := start) (recv := .ref Boot.mainId) (name := decl.name)
    (StateOk_reCtl hm _ []) rfl [] []
    (by
      intro σ hσ
      simp only [List.nil_append, List.mem_map] at hσ
      obtain ⟨p, hp, rfl⟩ := hσ
      exact (hps p hp).1)
    trivial hfinish
  have hselfm : start.currentFrame.self = .ref Boot.mainId := (hm.runtime hstart).self
  change StepSpec start Γ' τ
    (Interp.startArgs start start.currentFrame.self .implicit decl.name [] (toRubyList args) .none) κ' I'
  rw [hselfm]
  exact hh

#print axioms SemSafeCtxA.callSig
end Ratchet.Denote.Typed
