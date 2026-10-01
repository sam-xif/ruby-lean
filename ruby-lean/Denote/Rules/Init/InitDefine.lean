import Denote.Rules.Instance.MemberDefine
import Denote.Rules.Init.InitRun

/-! Initializer definitions: the allocation-anchored body contract. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.initializerDecl {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam} (hinit : d.name = "initialize")
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (_hout : FirstOrder Ib = true)
    (_hbody : SemInitA (initializerBodyCtx (instanceDeclCtx κ c d) c.name) ps .ivar0 d.body τ
      (initializerBodyCtx (instanceDeclCtx κ c d) c.name) Γb Ib)
    (hr : κ.scope.runtimeClass = some c.name) (hc : c ∈ κ.classes)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true) (hroot : c.name ∉ rootAncestors)
    (hf : memberFreshB κ c d = true) (htab : memberTableFrameB κ.classes c d = true) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I :=
  member_definition hr (by rw [hinit]; decide) (fun _ hm =>
    StateOk_install_member hm hr hc ht hΓ ha hplain hroot hf htab
      (by rw [hinit]; decide) (by rw [hinit]; decide) (by rw [hinit]; decide)
      (by rw [hinit]; decide) (by rw [hinit]; decide))

#print axioms SemSafeCtxA.initializerDecl
end Ratchet.Denote.Typed
