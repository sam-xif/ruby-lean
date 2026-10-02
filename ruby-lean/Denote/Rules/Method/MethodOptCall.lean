import Denote.Rules.Method.MethodOpt
import Denote.Rules.Method.MethodResolve
import Denote.Rules.Method.MethodArgs
import Denote.Rules.Method.MethodDefine

/-! Calls to a top-level method with one trailing optional parameter: the caller supplies
either the required arguments or one more, and the callee runs its default otherwise. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem toRubyParams_opt (ps : List SigParam) (n : String) (d : Ratchet.Expr) :
    toRubyParams (ps.map (fun p => Ratchet.Param.req p.1) ++ [.opt n d]) =
      (ps.map (·.1)).map RubyCore.Param.req ++ [.opt n (toRuby d)] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simpa only [List.map_cons, List.cons_append, toRubyParams, toRubyParam] using
      congrArg (RubyCore.Param.req p.1 :: ·) ih

theorem top_opt_method_stepSpec {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {m : Machine}
    {decl : Defn} {args : List Value} {ps : List SigParam} {n : String} {d : Ratchet.Expr}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1) ++ [.opt n d])
    (hps : ∀ p ∈ ps ++ [(n, σ)], FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hdflt : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I d σ
      (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I)
    (hbody : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩))
      (ps ++ [(n, σ)]) I decl.body τ
      (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I)
    (hafter : envAfter ps n σ = ps ++ [(n, σ)]) (hkill : killClosOverSpine I n σ = I)
    (hcapS : capStale n σ σ = false)
    (hctx : capStaleCtx n σ (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) = false)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = [])
    (hargs : (args.length = ps.length ∧ DenAll (ps.map (·.2)) m args) ∨
      (args.length = ps.length + 1 ∧ DenAll ((ps ++ [(n, σ)]).map (·.2)) m args))
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    StepSpec m Γ τ
      (Interp.finishSend m m.currentFrame.self .implicit decl.name args .none) κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready
  cases hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref Boot.mainId))).takeWhile (· != Boot.objectId))
      decl.name with
  | some cname =>
    rw [ready.self, finishSend_ordinary_shadow ready.payload hl hcode.builtin hu
      hcode.fromPrelude hs]
    trivial
  | none =>
    have hdef : md.definee.getD Boot.objectId = Boot.objectId := by
      simpa only [hcode.owner] using hcode.definee
    obtain ⟨next, he, hr⟩ := opt_method_runSpec (name := decl.name)
      (fr := some ⟨"Object", "Object", decl.name, false⟩) (d := d) (e := decl.body)
      hm ht ha hkont (hp.trans (by rw [hparams]; exact toRubyParams_opt ps n d))
      hcode.captured hcode.declared hb hcode.fromBlock hcode.forTargets hcode.superScope
      (by rw [hcode.owner]; exact hdef) hps hτ hΓ
      (fun names vs => by simp [frameScope, requiredFrame, hcode.owner, hcode.cref,
        hdef, hcode.fromPrelude, ready.owner, ready.cref, ready.captured,
        ready.origin, hm.localAlias, hblk, hcode.definitionFrame, ready.defFrame])
      (fun x => (constGet?_empty (κ := κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) hc x).trans
        (constGet?_empty hc x).symm)
      (fun names vs => by
        simp only [FrameOk, Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM,
          currentFrame_pushMethodFrame, requiredFrame, hcode.superName, Option.getD_none]
        exact ⟨trivial, by rw [ready.self]; exact ready.object, trivial⟩)
      hdflt hbody hafter hkill hcapS hctx hargs
    rw [ready.self] at he ⊢
    rw [finishSend_ordinary_userMethod ready.payload hl hcode.builtin hu hcode.fromPrelude hs]
    rw [he]
    exact hr

#print axioms top_opt_method_stepSpec
theorem SemSafeCtxA.callSigOpt {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ σ : Ty}
    {decl : Defn} {ps : List SigParam} {n : String} {d : Ratchet.Expr}
    {args : List Ratchet.Expr} {tys : List Ty}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1) ++ [.opt n d])
    (hps : ∀ p ∈ ps ++ [(n, σ)], FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hdflt : SemSafeCtxA (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I' d σ
      (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I')
    (hbody : SemSafeCtxA (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩))
      (ps ++ [(n, σ)]) I' decl.body τ
      (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I')
    (hafter : envAfter ps n σ = ps ++ [(n, σ)]) (hkill : killClosOverSpine I' n σ = I')
    (hcapS : capStale n σ σ = false)
    (hctx : capStaleCtx n σ (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) = false)
    (hargs : SemAllCtxA κ Γ I args tys κ' Γ' I')
    (htys : tys = ps.map (·.2) ∨ tys = (ps ++ [(n, σ)]).map (·.2))
    (hd : decl ∈ κ'.defs)
    (hstart : κ.scope.runtimeMain = true) (hruntime : κ'.scope.runtimeMain = true)
    (hself : κ'.selfTy = none) (hblock : κ'.blockTy = none) (hconst : κ'.consts = [])
    (hasms : κ'.asms = []) (hI : FirstOrder I' = true)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send none decl.name args none) τ κ' Γ' I' := by
  intro m hm
  let start := evalFrom m (.send none decl.name args none)
  have hfinish (n' : Machine) (hn : StateOk κ' Γ' I' n') (hk : n'.kont = [])
      (vs : List Value) (hv : DenAll tys n' vs) :
      StepSpec n' Γ' τ (Interp.finishSend n' (.ref Boot.mainId) .implicit decl.name vs .none) κ' I' := by
    have hlen := denAll_length hv
    have hargs' : (vs.length = ps.length ∧ DenAll (ps.map (·.2)) n' vs) ∨
        (vs.length = ps.length + 1 ∧ DenAll ((ps ++ [(n, σ)]).map (·.2)) n' vs) := by
      rcases htys with rfl | rfl
      · exact .inl ⟨by simpa using hlen, hv⟩
      · exact .inr ⟨by simpa using hlen, hv⟩
    have h := top_opt_method_stepSpec hparams hps hτ hdflt hbody hafter hkill hcapS hctx hn hd
      (ReframeFO.empty hI hself hblock hconst) hasms hconst hΓ hk hargs' hruntime hblock
    simpa only [(hn.runtime hruntime).self] using h
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  have hh := hargs.startArgs (m := start) (recv := .ref Boot.mainId) (name := decl.name)
    (StateOk_reCtl hm _ []) rfl [] []
    (by
      intro τ' hτ'
      simp only [List.nil_append] at hτ'
      rcases htys with rfl | rfl <;>
      · simp only [List.mem_map] at hτ'
        obtain ⟨p, hp, rfl⟩ := hτ'
        first
        | exact (hps p (List.mem_append_left _ hp)).1
        | exact (hps p hp).1)
    trivial hfinish
  have hselfm : start.currentFrame.self = .ref Boot.mainId := (hm.runtime hstart).self
  change StepSpec start Γ' τ
    (Interp.startArgs start start.currentFrame.self .implicit decl.name [] (toRubyList args) .none) κ' I'
  rw [hselfm]
  exact hh

#print axioms SemSafeCtxA.callSigOpt
/-- Definition installs the method; the default and body are rechecked at each call. -/
theorem SemSafeCtxA.defDeclOpt {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {d : Defn} {ps : List SigParam}
    {n : String} {dflt : Ratchet.Expr}
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1) ++ [.opt n dflt])
    (_hps : ∀ p ∈ ps ++ [(n, σ)], FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true)
    (_hdflt : SemSafeCtxA (topBodyCtx κ d) ps I dflt σ (topBodyCtx κ d) ps I)
    (_hbody : SemSafeCtxA (topBodyCtx κ d) (ps ++ [(n, σ)]) I d.body τ (topBodyCtx κ d) Γb I)
    (hruntime : κ.scope.runtimeMain = true) (hclasses : topDeclClassesB κ d.name = true)
    (hself : κ.selfTy = none) (hblock : κ.blockTy = none) (hconst : κ.consts = [])
    (hasms : κ.asms = []) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (topDeclCtx κ d) Γ I :=
  top_definition hruntime hclasses hself hblock hconst hasms hI hΓ hfresh hmiss hquiet

#print axioms SemSafeCtxA.defDeclOpt
end Ratchet.Denote.Typed
