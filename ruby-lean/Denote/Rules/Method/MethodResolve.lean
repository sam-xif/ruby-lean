import Denote.Rules.Method.MethodDispatch
import Denote.Rules.Primitive.PrimitiveStep

/-! Installed-method resolution and semantic body application, below the syntactic bridge.
This layer can discharge a registry rule without importing a checked `DJudge` artifact. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem lookup_go_own {h : Heap} {name : String} {owner : ObjId}
    {rest : List ObjId} {md : MethodDef} {fuel : Nat} {fallback : Bool}
    (hm : (h.classPayload? owner).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md)
    (hv : md.visibilityOnly = false) :
    lookupInChain.go h name (fuel + 1) (owner :: rest) fallback = some (owner, md) := by
  cases hc : h.classPayload? owner with
  | none => simp [hc] at hm
  | some cp =>
    cases hf : cp.methods.find? (·.1 == name) with
    | none => simp [hc, hf] at hm
    | some p =>
      simp only [hc, Option.bind_some, hf, Option.map_some, Option.some.injEq] at hm
      simp only [lookupInChain.go, hc, hf, hm, hv, Bool.not_false, ↓reduceIte]

theorem lookup_own_first {h : Heap} {recv : Value} {name : String} {owner : ObjId}
    {rest : List ObjId} {md : MethodDef}
    (ha : ancestors h (classOf h recv) = owner :: rest)
    (hm : (h.classPayload? owner).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md)
    (hv : md.visibilityOnly = false) :
    lookup h recv name = some (owner, md) := by
  unfold lookup
  rw [ha]
  exact lookup_go_own hm hv

/-- One absent singleton entry is followed by the checked defining class. The
runtime's fuel still decreases for that first class, even when its table is empty. -/
theorem lookup_after_empty {h : Heap} {recv : Value} {name : String} {k owner : ObjId}
    {rest : List ObjId} {md : MethodDef}
    (ha : ancestors h (classOf h recv) = k :: owner :: rest)
    (hn : (h.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = none)
    (hm : (h.classPayload? owner).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md)
    (hv : md.visibilityOnly = false) :
    lookup h recv name = some (owner, md) := by
  unfold lookup
  rw [ha]
  unfold lookupInChain
  cases hc : h.classPayload? k with
  | none => simpa only [lookupInChain.go, hc] using
      (lookup_go_own (fuel := 2 * h.objs.size) (fallback := false) (rest := rest) hm hv)
  | some cp =>
    have hf : cp.methods.find? (·.1 == name) = none := by
      cases he : cp.methods.find? (·.1 == name) with
      | none => rfl
      | some p => simp [hc, he] at hn
    simpa only [lookupInChain.go, hc, hf] using
      (lookup_go_own (fuel := 2 * h.objs.size) (fallback := false) (rest := rest) hm hv)

theorem defsOk_lookup {D : DefTable} {m : Machine} {decl : Defn}
    (hm : DefsOk D m) (hd : decl ∈ D) (ready : MainReady m) :
    ∃ md, lookup m.heap (.ref Boot.mainId) decl.name = some (Boot.objectId, md) ∧
      md.params = toRubyParams decl.params ∧ md.body = toRuby decl.body ∧
      md.undefined = false ∧ TopMethodCode md := by
  obtain ⟨hn, md, hl, hp, hb, hu, hcode⟩ := hm decl hd
  exact ⟨md, lookup_after_empty ready.chain
    ((mainOwnNamesB_iff.mp ready.mainNames).no_entry hn) hl hcode.visibilityOnly,
    hp, hb, hu, hcode⟩

theorem top_method_runSpec {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine} {decl : Defn}
    {args : List Value} {ps : List SigParam}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I decl.body τ
      (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = []) (hlen : args.length = ps.length)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none)
    (hshadow : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref Boot.mainId))).takeWhile (· != Boot.objectId))
      decl.name = none) :
    ∃ next, Interp.finishSend m m.currentFrame.self .implicit decl.name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready
  have hdef : md.definee.getD Boot.objectId = Boot.objectId := by
    simpa only [hcode.owner] using hcode.definee
  obtain ⟨next, he, hr⟩ := required_method_runSpec (name := decl.name)
    (fr := some ⟨"Object", "Object", decl.name, false⟩)
    hm ht ha hkont (hp.trans (by rw [hparams]; exact toRubyParams_required ps))
    hcode.captured hcode.declared hb hcode.fromBlock hcode.forTargets hlen hargs hps hτ hΓ
    (by simp [frameScope, requiredFrame, hcode.owner, hcode.cref,
      hdef, hcode.fromPrelude, ready.owner, ready.cref, ready.captured,
      ready.origin, hm.localAlias, hblk, hcode.definitionFrame, ready.defFrame])
    (fun x => (constGet?_empty (κ := κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) hc x).trans
      (constGet?_empty hc x).symm)
    (by
      simp only [FrameOk, Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM, currentFrame_pushMethodFrame, requiredFrame, hcode.superName, Option.getD_none]
      exact ⟨trivial, by rw [ready.self]; exact ready.object, trivial⟩)
    hbody
  refine ⟨next, ?_, hr⟩
  rw [ready.self] at he ⊢
  rw [finishSend_ordinary_userMethod ready.payload hl hcode.builtin hu hcode.fromPrelude
    hshadow]
  exact he

theorem top_method_stepSpec {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine} {decl : Defn}
    {args : List Value} {ps : List SigParam}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I decl.body τ
      (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = []) (hlen : args.length = ps.length)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none)
    : StepSpec m Γ τ
      (Interp.finishSend m m.currentFrame.self .implicit decl.name args .none) κ I := by
  have ready := hm.runtime hruntime
  cases hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref Boot.mainId))).takeWhile (· != Boot.objectId))
      decl.name with
  | none =>
    obtain ⟨next, he, hr⟩ := top_method_runSpec hparams hps hτ hbody hm hd ht ha hc hΓ
      hkont hlen hargs hruntime hblock hs
    rw [he]
    exact hr
  | some cname =>
    obtain ⟨md, hl, _, _, hu, hcode⟩ := defsOk_lookup hm.defs hd ready
    rw [ready.self, finishSend_ordinary_shadow ready.payload hl hcode.builtin hu
      hcode.fromPrelude hs]
    trivial

#print axioms top_method_stepSpec
#print axioms defsOk_lookup
#print axioms top_method_runSpec
end Ratchet.Denote.Typed
