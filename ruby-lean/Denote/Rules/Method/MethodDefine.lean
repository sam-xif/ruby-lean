import Ratchet.Guards.MethodCtx
import Denote.Sem.Instance.MethodInstall
import Denote.Rules.Method.MethodDispatch

/-! The annotation-checked definition rule's semantic obligation. Defining a method does
not execute its body, but the rule still requires that body at its entire declared domain.
No checker/registry admission is made by this module alone. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.defDecl {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {d : Defn} {ps : List SigParam}
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true)
    (_hbody : SemSafeCtxA (topBodyCtx κ d) ps I d.body τ (topBodyCtx κ d) Γb I)
    (hruntime : κ.scope.runtimeMain = true) (hclasses : κ.classes = [])
    (hself : κ.selfTy = none) (hblock : κ.blockTy = none) (hconst : κ.consts = [])
    (hasms : κ.asms = []) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (topDeclCtx κ d) Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  have ready := hm.runtime hruntime
  let md := definedMethod m d.name (toRubyParams d.params) (toRuby d.body)
  let n := installMethod m d.name (toRubyParams d.params) (toRuby d.body)
  have hreserved : StateOk (reserveNameCtx κ d.name) Γ I m := StateOk_reserveName hm d.name
  have hname : nameFreeN (reserveNameCtx κ d.name) d.name = false := by
    change (!κ.negUnpinned && !(d.name :: κ.declared).contains d.name) = false
    simp
  have hn : StateOk (topDeclCtx κ d) Γ I n := by
    have hh := StateOk_defineTopMethod (d := d) (md := md) hreserved
      (ReframeFO.empty hI hself hblock hconst) hΓ hasms hclasses hname hmiss hquiet
      ready.classLive hfresh rfl rfl rfl (definedMethod_code ready.owner ready.cref ready.phase)
    simpa only [topDeclCtx, reserveNameCtx, Ctx.defs, n, installMethod, ready.owner, md] using hh
  have hstep : Interp.stepFn (evalFrom m (.def' d.name d.params d.body)) =
      .next (deliverA (.val (.sym d.name)) n []) := by
    have hq : DefHookQuiet (evalFrom m (.def' d.name d.params d.body)) :=
      mainReady_defHookQuiet (m := m) ready
    have hs := step_def_install (name := d.name) (ps := toRubyParams d.params)
      (body := toRuby d.body) rfl (defHookQuiet_install hquiet hq)
    simpa only [n, installMethod, evalFrom, toRuby, deliverA, Interp.withCtl,
      reCtl, definedMethod, Machine.currentFrame, Answer.ctl] using hs
  refine ⟨n, .sym d.name, hstep, ?_, by simp [AnsOk, denM, isSymV], fun _ _ => hn⟩
  exact Framed_defineMethod m m.currentFrame.defmod d.name md

#print axioms SemSafeCtxA.defDecl
end Ratchet.Denote.Typed
