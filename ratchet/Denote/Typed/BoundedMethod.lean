import Denote.Typed.BoundedRun
import Denote.Typed.MethodResolve

/-! The ordinary method boundary consumes bounded body proofs. Installation, lookup,
annotation binding, framing, and caller restoration use the existing transport lemmas. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem methodFrame_runSpecAt {N : Nat} {m : Machine} {f : RubyCore.Frame} {e : Ratchet.Expr}
    {Γb Γ : Env} {κb κ : Ctx} {Ib I τ : Ty}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (ht : FirstOrder τ = true)
    (hb : RunSpecAt N (pushMethodFrame m f) (evalFrom (pushMethodFrame m f) e) Γb τ κb Ib)
    (hs : ∀ n v, ResultOk (pushMethodFrame m f) Γb τ (.val v) n κb Ib →
      StateOk κ Γ I (popMethodFrame n)) :
    RunSpecAt N m (pushK [.frameK m.frames.size] (evalFrom (pushMethodFrame m f) e)) Γ τ κ I := by
  apply hb.bindSpec (by
    intro k hk tag
    simp only [List.mem_singleton] at hk
    subst hk
    simp)
  intro a n hr
  exact (methodFrame_continue_spec hl hc ht hs hr).at N

theorem required_method_runSpecAt {N : Nat} {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine}
    {md : MethodDef} {name : String} {ps : List SigParam} {args : List Value}
    {e : Ratchet.Expr} {fr : Option Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = []) (hp : md.params = (ps.map (·.1)).map RubyCore.Param.req)
    (hcap : md.capturedFrame = none) (hdecl : md.declared = []) (hbody : md.body = toRuby e)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hscope : frameScope (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args) =
      frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hframe : FrameOk fr
      (pushMethodFrame m (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args)))
    (hb : SemSafeCtxAt N (κ.withFrame fr) ps I e τ (κ.withFrame fr) Γb I) :
    ∃ next, Interp.enterUserMethod m m.currentFrame.self name md args none = .next next ∧
      RunSpecAt N m next Γ τ κ I := by
  let f := requiredFrame m.currentFrame.self name md (ps.map (·.1)) args
  let entry := pushMethodFrame m f
  have he : StateOk (κ.withFrame fr) ps I entry :=
    method_enter_state hm ht ha (congrArg FrameScope.self hscope)
      (congrArg FrameScope.blk hscope) (congrArg FrameScope.cref hscope)
      (congrArg FrameScope.defmod hscope) (congrArg FrameScope.captured hscope) hk
      (requiredFrame_envOk m _ name md ps args hlen hargs hps) hframe
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (congrArg FrameScope.captured hscope).symm
  have hs := methodFrame_runSpecAt hm.frameInRange.2 (f := f) rfl hτ (hb entry he)
    (fun n v hr => method_pop_state hm ht ha hu rfl hscope hk hΓ hr.1 (hr.2.2 v rfl))
  refine ⟨_, ?_, hs⟩
  rw [enterUserMethod_required m _ name md (ps.map (·.1)) args hp hcap hdecl
    (by simpa using hlen)]
  simp only [Interp.withKont, pushK, evalFrom, f, pushMethodFrame, hkont, hbody, List.nil_append]


theorem top_method_runSpecAt {N : Nat} {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine} {decl : Defn}
    {args : List Value} {ps : List SigParam}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxAt N (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) ps I decl.body τ
      (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) Γb I)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = []) (hlen : args.length = ps.length)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    ∃ next, Interp.finishSend m m.currentFrame.self .implicit decl.name args .none = .next next ∧
      RunSpecAt N m next Γ τ κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready.chain
  obtain ⟨next, he, hr⟩ := required_method_runSpecAt (name := decl.name)
    (fr := some ⟨"Object", "Object", decl.name⟩)
    hm ht ha hkont (hp.trans (by rw [hparams]; exact toRubyParams_required ps))
    hcode.captured hcode.declared hb hlen hargs hps hτ hΓ
    (by simp [frameScope, requiredFrame, hcode.owner, hcode.cref,
      ready.owner, ready.cref, ready.captured, hblk])
    (fun x => (constGet?_empty (κ := κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) hc x).trans
      (constGet?_empty hc x).symm)
    (by
      simp only [FrameOk, currentFrame_pushMethodFrame, requiredFrame, hcode.superName, Option.getD_none]
      exact ⟨trivial, by rw [ready.self]; exact ready.object⟩)
    hbody
  refine ⟨next, ?_, hr⟩
  rw [ready.self] at he ⊢
  rw [finishSend_ordinary_userMethod ready.payload hl hcode.builtin hu hcode.fromPrelude
    (by simp [ready.chain, Interp.crubyShadow]; rfl)]
  exact he


#print axioms methodFrame_runSpecAt
#print axioms required_method_runSpecAt
#print axioms top_method_runSpecAt
end Ratchet.Denote.Typed
