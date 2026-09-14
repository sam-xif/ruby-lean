import Denote.Typed.MethodDispatch

/-! Installed-method resolution and semantic body application, below the syntactic bridge.
This layer can discharge a registry rule without importing a checked `DJudge` artifact. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem lookup_own_first {h : Heap} {recv : Value} {name : String} {owner : ObjId}
    {rest : List ObjId} {md : MethodDef}
    (ha : ancestors h (classOf h recv) = owner :: rest)
    (hm : (h.classPayload? owner).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md) :
    lookup h recv name = some (owner, md) := by
  unfold lookup
  rw [ha, lookup.go]
  cases hc : h.classPayload? owner with
  | none => simp [hc] at hm
  | some cp =>
    cases hf : cp.methods.find? (·.1 == name) with
    | none => simp [hc, hf] at hm
    | some p =>
      simp only [hc, Option.bind_some, hf, Option.map_some, Option.some.injEq] at hm
      simp only [hf, hm]

theorem defsOk_lookup {D : DefTable} {m : Machine} {decl : Defn} {recv : Value}
    {rest : List ObjId} (hm : DefsOk D m) (hd : decl ∈ D)
    (ha : ancestors m.heap (classOf m.heap recv) = Boot.objectId :: rest) :
    ∃ md, lookup m.heap recv decl.name = some (Boot.objectId, md) ∧
      md.params = toRubyParams decl.params ∧ md.body = toRuby decl.body ∧
      md.undefined = false ∧ TopMethodCode md := by
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := hm decl hd
  exact ⟨md, lookup_own_first ha hl, hp, hb, hu, hcode⟩

theorem top_method_runSpec {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine} {decl : Defn}
    {args : List Value} {ps : List SigParam}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) ps I decl.body τ
      (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) Γb I)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = []) (hlen : args.length = ps.length)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    ∃ next, Interp.finishSend m m.currentFrame.self .implicit decl.name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready.chain
  obtain ⟨next, he, hr⟩ := required_method_runSpec (name := decl.name)
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

#print axioms defsOk_lookup
#print axioms top_method_runSpec
end Ratchet.Denote.Typed
