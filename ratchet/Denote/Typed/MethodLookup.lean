import Denote.Typed.MethodChecked
import Denote.Typed.MethodDispatch

/-! Recover the actual method from conformance, then consume its checked body. The call
does not receive an independently chosen `MethodDef` or assume dispatch reaches that body. -/

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

/-- Every listed definition resolves at the head of the ordinary Object chain, including
the runtime flags that ensure its body and annotation environment are actually used. -/
theorem defsOk_lookup {D : DefTable} {m : Machine} {decl : Defn} {recv : Value}
    {rest : List ObjId} (hm : DefsOk D m) (hd : decl ∈ D)
    (ha : ancestors m.heap (classOf m.heap recv) = Boot.objectId :: rest) :
    ∃ md, lookup m.heap recv decl.name = some (Boot.objectId, md) ∧
      md.params = toRubyParams decl.params ∧ md.body = toRuby decl.body ∧
      md.undefined = false ∧ TopMethodCode md := by
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := hm decl hd
  exact ⟨md, lookup_own_first ha hl, hp, hb, hu, hcode⟩

/-- Ordinary top-level dispatch uses the installed table and the stored body derivation.
All physical-frame facts now come from conformance at the requested runtime scope. -/
theorem checked_top_call {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {decl : Defn}
    {args : List Value}
    (c : CheckedBody (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) I decl)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = []) (hlen : args.length = c.params.length)
    (hargs : DenAll (c.params.map (·.2)) m args)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    ∃ next, Interp.finishSend m m.currentFrame.self .implicit decl.name args .none = .next next ∧
      RunSpec m next Γ c.ret κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready.chain
  obtain ⟨next, he, hr⟩ := checked_method_runSpec c hm ht ha hkont hp hcode.captured hcode.declared hb
    hlen hargs hΓ
    (by simp [frameScope, requiredFrame, hcode.owner, hcode.cref,
      ready.owner, ready.cref, ready.captured, hblk])
    (fun x => (constGet?_empty (κ := κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) hc x).trans
      (constGet?_empty hc x).symm)
    (by
      simp only [FrameOk, currentFrame_pushMethodFrame, requiredFrame, hcode.superName, Option.getD_none]
      exact ⟨trivial, by rw [ready.self]; exact ready.object⟩)
  refine ⟨next, ?_, hr⟩
  rw [ready.self] at he ⊢
  rw [finishSend_ordinary_userMethod ready.payload hl hcode.builtin hu hcode.fromPrelude
    (by simp [ready.chain, Interp.crubyShadow]; rfl)]
  exact he

#print axioms defsOk_lookup
#print axioms checked_top_call
end Ratchet.Denote.Typed
